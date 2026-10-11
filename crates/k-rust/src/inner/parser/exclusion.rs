//! The relation filter's exclusions: which node may not stand as which child of which other node,
//! in one definition read by every parser krust builds from a grammar.
//!
//! A K grammar states its disambiguation as relations between labels: priorities, the
//! associativity groups, and the fixed scopes of K's own rewrite, sequence, `#let` and cast
//! syntax. They decide nothing until a position selection says where in a node they apply and a
//! node notion says which production's node stands at that position. The in-process parser
//! judges a parse forest with them ([`Grammar::filter_packed_priority`](super::Grammar)), and
//! the Bison exporter compiles the same judgements into restricted copies of the operand sorts,
//! so that the generated parser never builds an excluded edge. Both read this module: the
//! node notion ([`NodeShape::passes_child_through`], [`NodeShape::judged_as_child`]), the
//! position selection ([`NodeShape::judged_side`]) and the judgement of one edge
//! ([`Exclusions::violation`]), so the two parsers exclude the same edges by construction.

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::definition::{AssociativityRelations, PartialOrder};
use crate::kast::{GeneratedLabel, InternalLabel};

/// The parent labels a nested `#KRewrite` may appear under.
const SCOPE_REWRITE: [InternalLabel; 6] = [
    InternalLabel::RuleRequires,
    InternalLabel::RuleEnsures,
    InternalLabel::RuleRequiresEnsures,
    InternalLabel::KRewrite,
    InternalLabel::WithConfig,
    InternalLabel::KList,
];

/// The parent labels a nested `#KSequence` may appear under.
const SCOPE_SEQUENCE: [InternalLabel; 6] = [
    InternalLabel::RuleRequires,
    InternalLabel::RuleEnsures,
    InternalLabel::RuleRequiresEnsures,
    InternalLabel::KRewrite,
    InternalLabel::KSequence,
    InternalLabel::KList,
];

/// The parent labels a nested `#let` may appear under.
const SCOPE_LET: [InternalLabel; 7] = [
    InternalLabel::RuleRequires,
    InternalLabel::RuleEnsures,
    InternalLabel::RuleRequiresEnsures,
    InternalLabel::KRewrite,
    InternalLabel::KSequence,
    InternalLabel::Let,
    InternalLabel::KList,
];

/// The side of a parent's node at which the relation filter judges a child
/// ([`NodeShape::judged_side`]): associativity applies at the two ends only.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Side {
    Left,
    Right,
    Middle,
}

/// What a production's node is to the relation filter: the facts about the production that
/// decide whether it builds a node, where the filter judges the node's children, and how a
/// relation names it. Every parser describes its productions this way and asks the methods
/// below, so none of them restates a rule.
#[derive(Clone, Copy, Debug)]
pub(crate) struct NodeShape<'a> {
    /// The label the relations name the node by: its semantic label, else a bracket's label.
    pub(crate) parse_label: Option<&'a String>,
    /// Whether the production has a semantic label (a bracket's label is no semantic label).
    pub(crate) labelled: bool,
    pub(crate) token: bool,
    pub(crate) bracket: bool,
    pub(crate) transparent: bool,
    /// Whether the production is generated record syntax, whose node is collapsed into the
    /// production it stands for before its edges are judged.
    pub(crate) record: bool,
    /// The number of items.
    pub(crate) items: usize,
    /// The number of nonterminal items, which is the number of the node's children.
    pub(crate) nonterminals: usize,
    /// Whether the first item is a nonterminal.
    pub(crate) first_nonterminal: bool,
    /// Whether the last item is a nonterminal.
    pub(crate) last_nonterminal: bool,
    /// The positions (1-based, among the nonterminals) the production's `applyPriority` names.
    pub(crate) apply_priority: Option<&'a BTreeSet<usize>>,
}

impl NodeShape<'_> {
    /// Whether the production is a syntactic subsort: one nonterminal and no terminal, labelled
    /// or not. It puts a phrase of its nonterminal's sort where its result sort is expected with
    /// nothing written around it, so the phrase's own operators are not nested inside anything
    /// the text shows, and the filter judges no edge below it. A bracket writes its delimiters,
    /// so it is none.
    pub(crate) fn syntactic_subsort(&self) -> bool {
        !self.bracket && self.items == 1 && self.nonterminals == 1
    }

    /// Whether a node of this production is its only child itself: an unlabelled or transparent
    /// production with one nonterminal that is not a token, record or bracket denotes its child
    /// and adds no node, so the filter judges the child wherever this production stands.
    pub(crate) fn passes_child_through(&self) -> bool {
        !self.token
            && !self.record
            && !self.bracket
            && (self.transparent || !self.labelled)
            && self.nonterminals == 1
    }

    /// Whether a node of this production is judged where it stands as a child: not a token's
    /// leaf (no relation names one), not a record's node (judged after it collapses into the
    /// production it stands for), and a node at all ([`Self::passes_child_through`]).
    pub(crate) fn judged_as_child(&self) -> bool {
        !self.token && !self.record && !self.passes_child_through()
    }

    /// The side at which the relation filter judges the child at `position` (1-based, among
    /// the children) of a node of this production that has `child_count` children, or `None`
    /// where it judges none. This is the filter's one position selection: the node judges
    /// nothing below it when it is a record or a syntactic subsort; else it judges the
    /// positions its `applyPriority` names, or by default its first and last child where that
    /// child is the first or the last item, because only there can an operator written next to
    /// the node's own text be read as nested on either side. A judged child is on the left side
    /// when it is the first item, on the right side when it is the last item, and in the middle
    /// otherwise.
    pub(crate) fn judged_side(&self, position: usize, child_count: usize) -> Option<Side> {
        if self.record || self.syntactic_subsort() {
            return None;
        }
        let first = position == 1 && self.first_nonterminal;
        let last = position == child_count && self.last_nonterminal;
        let judged = match self.apply_priority {
            Some(positions) => positions.contains(&position),
            None => first || last,
        };
        judged.then_some(if first {
            Side::Left
        } else if last {
            Side::Right
        } else {
            Side::Middle
        })
    }
}

/// Why the relation filter rejects a child at an edge ([`Exclusions::violation`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Exclusion {
    /// A rewrite, sequence or `#let` below a parent outside the scope K's syntax gives it.
    Scope,
    /// A cast over a child whose text ends with a nonterminal: the cast would bind tighter than
    /// the child's own last operand.
    CastPriority,
    /// The child has lesser priority than the parent.
    Priority,
    /// The child is in an associativity group of the parent that excludes it on this side.
    Associativity(Side),
}

/// The relations of one grammar, with the labels that occur in an associativity relation
/// numbered so that a pair of them is looked up without copying either label.
#[derive(Clone, Debug)]
pub(crate) struct Exclusions {
    priorities: PartialOrder<String>,
    /// The number of each label that occurs in an associativity relation.
    ids: FxHashMap<String, u32>,
    /// The `(parent, child)` pairs where `child` may not be `parent`'s right child (`left`
    /// associativity, or non-associativity).
    left: FxHashSet<(u32, u32)>,
    /// The `(parent, child)` pairs where `child` may not be `parent`'s left child (`right`
    /// associativity, or non-associativity).
    right: FxHashSet<(u32, u32)>,
}

impl Exclusions {
    pub(crate) fn new(
        priorities: PartialOrder<String>,
        associativities: &AssociativityRelations,
    ) -> Self {
        let mut ids = FxHashMap::<String, u32>::default();
        let mut index = |pairs: &BTreeSet<(String, String)>| {
            let mut id = |label: &String| {
                let next = u32::try_from(ids.len()).expect("fewer than 2^32 labels");
                *ids.entry(label.clone()).or_insert(next)
            };
            pairs
                .iter()
                .map(|(parent, child)| (id(parent), id(child)))
                .collect::<FxHashSet<_>>()
        };
        let left = index(&associativities.left);
        let right = index(&associativities.right);
        Self {
            priorities,
            ids,
            left,
            right,
        }
    }

    /// The number of `label`, when it occurs in an associativity relation.
    pub(crate) fn associativity_id(&self, label: &str) -> Option<u32> {
        self.ids.get(label).copied()
    }

    /// Whether the associativity relations forbid a node numbered `child` as the child of one
    /// numbered `parent` on `side`: a right-associative or non-associative group excludes its
    /// members as the left child, a left-associative or non-associative group as the right
    /// child, and no group judges a middle child.
    pub(crate) fn associativity_forbids(&self, parent: u32, child: u32, side: Side) -> bool {
        match side {
            Side::Left => self.right.contains(&(parent, child)),
            Side::Right => self.left.contains(&(parent, child)),
            Side::Middle => false,
        }
    }

    /// The exclusion that rejects a node of `child` as the child of a node of `parent` on
    /// `side`, if any. Both nodes are judged by their parse labels; a node without one is in no
    /// relation. `side` comes from the parent's [`NodeShape::judged_side`], and the child is a
    /// node judged where it stands ([`NodeShape::judged_as_child`]).
    pub(crate) fn violation(
        &self,
        parent: &NodeShape<'_>,
        child: &NodeShape<'_>,
        side: Side,
    ) -> Option<Exclusion> {
        let (Some(parent_label), Some(child_label)) = (parent.parse_label, child.parse_label)
        else {
            return None;
        };
        let allowed_parent = |exceptions: &[InternalLabel]| {
            // A bracket has a parse label for priority checks but no semantic label: the scopes
            // restrict a rewrite, sequence or `#let` only below a semantic constructor.
            parent.syntactic_subsort()
                || !parent.labelled
                || exceptions
                    .iter()
                    .any(|label| parent_label == label.as_str())
        };
        let scoped = [
            (InternalLabel::KRewrite, &SCOPE_REWRITE[..]),
            (InternalLabel::KSequence, &SCOPE_SEQUENCE[..]),
            (InternalLabel::Let, &SCOPE_LET[..]),
        ];
        if scoped.iter().any(|(scoped, exceptions)| {
            child_label == scoped.as_str() && !allowed_parent(exceptions)
        }) {
            return Some(Exclusion::Scope);
        }
        if (parent_label == InternalLabel::SyntacticCast.as_str()
            || matches!(
                GeneratedLabel::of_name(parent_label),
                Some(GeneratedLabel::SemanticCast { .. })
            ))
            && child.last_nonterminal
        {
            return Some(Exclusion::CastPriority);
        }
        if self.priorities.less_than(parent_label, child_label) {
            return Some(Exclusion::Priority);
        }
        let forbids = side != Side::Middle
            && self
                .associativity_id(parent_label)
                .zip(self.associativity_id(child_label))
                .is_some_and(|(parent, child)| self.associativity_forbids(parent, child, side));
        forbids.then_some(Exclusion::Associativity(side))
    }
}
