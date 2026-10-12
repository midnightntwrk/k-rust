//! ```toml algorithm
//! id = "parser.forest.pack"
//! name = "packed parse-forest construction"
//! sites = ["build_packed_term", "pack_alternatives", "PackedTerm::unpack"]
//! variable = "C = children packed; N = nodes unpacked"
//! counters = ["ParserUnpackedNodes"]
//! produces = [{ type = "k_rust::inner::parser::forest::PackedTerm", role = "packed forest" }]
//!
//! [[cost]]
//! mode = "construction and unpacking"
//! bound = "O(C + N)"
//! ```
//!
//! ```toml algorithm
//! id = "parser.forest.order"
//! name = "structural ordering of packed parse forests"
//! sites = ["cmp_packed_structurally", "packed_terms_in_structural_order", "StructuralOrder::sorted", "PackedTerm::cmp"]
//! variable = "N = compared subtree nodes when fingerprints tie; P = distinct node pairs reached by one structural comparison; A = alternatives of one compared ambiguity; n = terms in the ordered set"
//! counters = ["ParserPackedStructuralComparisons"]
//!
//! [[cost]]
//! mode = "PackedTerm::cmp"
//! bound = "O(1) unless the fingerprints tie, then O(N)"
//!
//! [[cost]]
//! mode = "cmp_packed_structurally"
//! bound = "O(P x A) plus one sort of the alternatives of each compared ambiguity, O(A log A) comparisons"
//!
//! [[cost]]
//! mode = "packed_terms_in_structural_order"
//! bound = "O(n log n) structural comparisons sharing one pair memo"
//!
//! [[cost]]
//! mode = "StructuralOrder::sorted, the orderings of one pass"
//! bound = "every distinct node pair the pass's orderings reach is compared once, O(A) per compared ambiguity pair after each compared ambiguity's alternatives are sorted once, O(A log A), plus O(n log n) memo lookups per ordered set"
//! ```
//!
//! ```toml algorithm
//! id = "parser.forest.intern"
//! name = "hash-consing of the nodes of a lowering session"
//! sites = ["LoweringSession::intern", "LoweringSession::intern_parsed", "LoweringSession::intern_forest"]
//! variable = "B = session nodes with the interned node's key (its fingerprint and the identities of its children or alternatives, or its own for a leaf); C = the interned node's children or alternatives; O = owned nodes of a tree; F = nodes of a packed forest; G = their child edges"
//! counters = []
//! no_counter = "session interning has no dedicated counter"
//!
//! [[cost]]
//! mode = "LoweringSession::intern"
//! bound = "one hash lookup and O(B x C) pointer comparisons; B is 1 unless keys collide"
//!
//! [[cost]]
//! mode = "LoweringSession::intern_parsed"
//! bound = "O(O) node constructions and interns"
//!
//! [[cost]]
//! mode = "LoweringSession::intern_forest"
//! bound = "O(F + G): each node interned once, after its children"
//! ```
//!
//! ```toml algorithm
//! id = "parser.disambiguation.reserve_names"
//! name = "reservation of variable names before record collapse"
//! sites = ["packed_variable_names"]
//! variable = "N = packed nodes"
//! counters = []
//! no_counter = "variable-name reservation has no dedicated counter"
//! span = "per problem"
//!
//! [[cost]]
//! mode = "one packed forest"
//! bound = "O(N)"
//! ```
//!
//! Packed parse forest with FNV fingerprints and deterministic structural ordering.
//!
//! Construction is O(children); `PackedTerm::cmp` is O(1) unless fingerprints tie, and
//! `cmp_packed_structurally` walks both subtrees with pair memoization.
//! `Counter::ParserPackedStructuralComparisons` and
//! `Counter::ParserUnpackedNodes` measure the two variable costs.

use std::collections::{BTreeSet, HashSet};
use std::rc::Rc;

use k_rust_kore::measure::{self, Algorithm, Counter};

use crate::kast::{FrontendSort, Sort, Term, TermMetadata};

#[cfg(test)]
use super::{PACKED_STRUCTURAL_COMPARISONS, UNPACKED_NODES};
use super::{ParseProvenance, Production, mint_literal_sort, term_metadata};

// stack-accepted(debug-only-checks): the derived `Debug` recurses once per tree level and is used only in test and diagnostic output. See docs/backend-port.md#stack-bounds.
/// An owned parse tree. Its copies and comparisons descend one level at a time under
/// `crate::stack::guarded` and its drop frees one node at a time, so a tree of any depth is
/// copied, compared and dropped on any thread.
#[derive(Debug)]
pub(super) enum ParsedTerm {
    Production {
        production: usize,
        children: Vec<ParsedTerm>,
        metadata: TermMetadata,
    },
    #[cfg_attr(not(feature = "z3-inference"), allow(dead_code))]
    InstantiatedProduction {
        production: usize,
        parameters: Vec<Sort>,
        children: Vec<ParsedTerm>,
        metadata: TermMetadata,
    },
    Term(Term),
    Ambiguity(BTreeSet<ParsedTerm>),
}

impl Clone for ParsedTerm {
    fn clone(&self) -> Self {
        crate::stack::guarded(|| match self {
            Self::Production {
                production,
                children,
                metadata,
            } => Self::Production {
                production: *production,
                children: children.clone(),
                metadata: metadata.clone(),
            },
            Self::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => Self::InstantiatedProduction {
                production: *production,
                parameters: parameters.clone(),
                children: children.clone(),
                metadata: metadata.clone(),
            },
            Self::Term(term) => Self::Term(term.clone()),
            Self::Ambiguity(alternatives) => Self::Ambiguity(alternatives.clone()),
        })
    }
}

/// Trees are ordered by variant (`Production`, `InstantiatedProduction`, `Term`, `Ambiguity`),
/// then by their fields in declaration order, as a derived order would.
impl Ord for ParsedTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let rank = |term: &Self| match term {
            Self::Production { .. } => 0,
            Self::InstantiatedProduction { .. } => 1,
            Self::Term(_) => 2,
            Self::Ambiguity(_) => 3,
        };
        crate::stack::guarded(|| match (self, other) {
            (
                Self::Production {
                    production,
                    children,
                    metadata,
                },
                Self::Production {
                    production: other_production,
                    children: other_children,
                    metadata: other_metadata,
                },
            ) => production
                .cmp(other_production)
                .then_with(|| children.cmp(other_children))
                .then_with(|| metadata.cmp(other_metadata)),
            (
                Self::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                },
                Self::InstantiatedProduction {
                    production: other_production,
                    parameters: other_parameters,
                    children: other_children,
                    metadata: other_metadata,
                },
            ) => production
                .cmp(other_production)
                .then_with(|| parameters.cmp(other_parameters))
                .then_with(|| children.cmp(other_children))
                .then_with(|| metadata.cmp(other_metadata)),
            (Self::Term(term), Self::Term(other_term)) => term.cmp(other_term),
            (Self::Ambiguity(alternatives), Self::Ambiguity(other_alternatives)) => {
                alternatives.cmp(other_alternatives)
            }
            _ => rank(self).cmp(&rank(other)),
        })
    }
}

impl PartialOrd for ParsedTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for ParsedTerm {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for ParsedTerm {}

/// Dropping an owned parse tree frees its nodes one at a time rather than recursing into them,
/// so a tree of any depth is dropped on any thread, including the subtrees a pass discards when
/// it fails part-way through a tree.
impl Drop for ParsedTerm {
    #[inline]
    fn drop(&mut self) {
        if !self.has_grandchildren() {
            // The fields' drops free a node whose children are leaves within one frame.
            return;
        }
        let mut work = Vec::new();
        self.detach_children(&mut work);
        // Invariant: `work` holds detached subtrees; each pop detaches its node's children into
        // `work`, so every node is dropped with no children left.
        while let Some(mut term) = work.pop() {
            term.detach_children(&mut work);
        }
    }
}

/// The owned fields of a [`ParsedTerm`], for a match that takes a tree apart by value: a tree
/// frees its nodes one at a time when dropped, so it cannot be destructured by move itself.
pub(super) enum ParsedParts {
    Production {
        production: usize,
        children: Vec<ParsedTerm>,
        metadata: TermMetadata,
    },
    #[cfg_attr(not(feature = "z3-inference"), allow(dead_code))]
    InstantiatedProduction {
        production: usize,
        parameters: Vec<Sort>,
        children: Vec<ParsedTerm>,
        metadata: TermMetadata,
    },
    Term(Term),
    Ambiguity(BTreeSet<ParsedTerm>),
}

impl ParsedTerm {
    /// Take this node apart into its owned fields, leaving an empty node to drop.
    pub(super) fn into_parts(mut self) -> ParsedParts {
        use std::mem::take;
        match &mut self {
            Self::Production {
                production,
                children,
                metadata,
            } => ParsedParts::Production {
                production: *production,
                children: take(children),
                metadata: take(metadata),
            },
            Self::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => ParsedParts::InstantiatedProduction {
                production: *production,
                parameters: take(parameters),
                children: take(children),
                metadata: take(metadata),
            },
            Self::Term(term) => {
                ParsedParts::Term(std::mem::replace(term, Term::Sequence(Vec::new())))
            }
            Self::Ambiguity(alternatives) => ParsedParts::Ambiguity(take(alternatives)),
        }
    }

    /// Whether this node has children: a production's arguments or an ambiguity's alternatives.
    fn has_children(&self) -> bool {
        match self {
            Self::Production { children, .. } | Self::InstantiatedProduction { children, .. } => {
                !children.is_empty()
            }
            Self::Ambiguity(alternatives) => !alternatives.is_empty(),
            Self::Term(_) => false,
        }
    }

    /// Whether a child of this node has children of its own.
    fn has_grandchildren(&self) -> bool {
        match self {
            Self::Production { children, .. } | Self::InstantiatedProduction { children, .. } => {
                children.iter().any(Self::has_children)
            }
            Self::Ambiguity(alternatives) => alternatives.iter().any(Self::has_children),
            Self::Term(_) => false,
        }
    }

    fn detach_children(&mut self, work: &mut Vec<Self>) {
        match self {
            Self::Production { children, .. } | Self::InstantiatedProduction { children, .. } => {
                work.append(children);
            }
            Self::Ambiguity(alternatives) => work.extend(std::mem::take(alternatives)),
            Self::Term(_) => {}
        }
    }
}

impl From<ParsedParts> for ParsedTerm {
    fn from(parts: ParsedParts) -> Self {
        match parts {
            ParsedParts::Production {
                production,
                children,
                metadata,
            } => Self::Production {
                production,
                children,
                metadata,
            },
            ParsedParts::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => Self::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            },
            ParsedParts::Term(term) => Self::Term(term),
            ParsedParts::Ambiguity(alternatives) => Self::Ambiguity(alternatives),
        }
    }
}

/// Shared parse-forest node used through the ordering-sensitive parser and Z3-inference pipeline.
///
/// Keeping children behind `Rc` prevents chart diamonds from expanding while record syntax,
/// priority, applications, rewrite preferences, ambiguities, and sort constraints are normalized.
/// Ambiguous forests are materialized as an owned [`ParsedTerm`] only after Z3 model application
/// has discarded ill-sorted branches.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum PackedNode {
    Production {
        production: usize,
        children: Vec<Rc<PackedTerm>>,
        metadata: TermMetadata,
    },
    #[cfg_attr(not(feature = "z3-inference"), allow(dead_code))]
    InstantiatedProduction {
        production: usize,
        parameters: Vec<Sort>,
        children: Vec<Rc<PackedTerm>>,
        metadata: TermMetadata,
    },
    Term(Term),
    Ambiguity(BTreeSet<Rc<PackedTerm>>),
}

#[derive(Clone, Debug)]
pub(super) struct PackedTerm {
    pub(super) fingerprint: u64,
    pub(super) node: PackedNode,
}

impl PartialEq for PackedTerm {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}

impl Eq for PackedTerm {}

impl PartialOrd for PackedTerm {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PackedTerm {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if std::ptr::eq(self, other) {
            return std::cmp::Ordering::Equal;
        }
        // The fingerprint is a fast ordering key, not an identity. Equal keys still compare the
        // complete structure, so even an FNV collision cannot merge distinct parses.
        self.fingerprint.cmp(&other.fingerprint).then_with(|| {
            measure::bump(Counter::ParserPackedStructuralComparisons);
            // Equal fingerprints compare the structure, which descends once per level.
            crate::stack::guarded(|| self.node.cmp(&other.node))
        })
    }
}

/// Dropping a packed node frees the nodes below it that it alone owns one at a time rather than
/// recursing into them, so the forest of a program of any depth is freed on any thread.
impl Drop for PackedTerm {
    fn drop(&mut self) {
        let mut work = Vec::new();
        self.node.detach_owned_children(&mut work);
        // Invariant: `work` holds detached children; each pop detaches the children of a child
        // this forest alone owns before that child is dropped, so every drop below is shallow.
        while let Some(mut child) = work.pop() {
            if let Some(child) = Rc::get_mut(&mut child) {
                child.node.detach_owned_children(&mut work);
            }
        }
    }
}

impl PackedNode {
    /// Move this node's children into `work` when one of them is owned by this node alone and
    /// has children of its own, the case in which dropping them in place would recurse.
    fn detach_owned_children(&mut self, work: &mut Vec<Rc<PackedTerm>>) {
        let owned_inner = |child: &Rc<PackedTerm>| {
            Rc::strong_count(child) == 1 && Rc::weak_count(child) == 0 && child.node.has_children()
        };
        match self {
            Self::Production { children, .. } | Self::InstantiatedProduction { children, .. } => {
                if children.iter().any(owned_inner) {
                    work.append(children);
                }
            }
            Self::Ambiguity(alternatives) => {
                if alternatives.iter().any(owned_inner) {
                    work.extend(std::mem::take(alternatives));
                }
            }
            Self::Term(_) => {}
        }
    }

    fn has_children(&self) -> bool {
        match self {
            Self::Production { children, .. } | Self::InstantiatedProduction { children, .. } => {
                !children.is_empty()
            }
            Self::Ambiguity(alternatives) => !alternatives.is_empty(),
            Self::Term(_) => false,
        }
    }
}

impl PackedTerm {
    pub(super) fn leaf(term: Term) -> Rc<Self> {
        let mut fingerprint = Fingerprint::new(2);
        fingerprint.write(term.to_string().as_bytes());
        Rc::new(Self {
            fingerprint: fingerprint.finish(),
            node: PackedNode::Term(term),
        })
    }

    pub(super) fn production(
        production: usize,
        children: Vec<Rc<Self>>,
        metadata: TermMetadata,
    ) -> Rc<Self> {
        let mut fingerprint = Fingerprint::new(0);
        fingerprint.write_usize(production);
        fingerprint.write_metadata(&metadata);
        for child in &children {
            fingerprint.write_u64(child.fingerprint);
        }
        Rc::new(Self {
            fingerprint: fingerprint.finish(),
            node: PackedNode::Production {
                production,
                children,
                metadata,
            },
        })
    }

    pub(super) fn instantiated_production(
        production: usize,
        parameters: Vec<Sort>,
        children: Vec<Rc<Self>>,
        metadata: TermMetadata,
    ) -> Rc<Self> {
        let mut fingerprint = Fingerprint::new(1);
        fingerprint.write_usize(production);
        fingerprint.write_metadata(&metadata);
        for parameter in &parameters {
            fingerprint.write(parameter.to_string().as_bytes());
        }
        for child in &children {
            fingerprint.write_u64(child.fingerprint);
        }
        Rc::new(Self {
            fingerprint: fingerprint.finish(),
            node: PackedNode::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            },
        })
    }

    pub(super) fn ambiguity(alternatives: BTreeSet<Rc<Self>>) -> Rc<Self> {
        if alternatives.len() == 1 {
            return alternatives
                .into_iter()
                .next()
                .expect("one packed alternative exists");
        }
        Self::alternatives(alternatives)
    }

    /// The ambiguity node over exactly `alternatives`, even when there is only one: the packed
    /// form of an owned `ParsedTerm::Ambiguity` as written, which [`Self::ambiguity`] would
    /// collapse. A pass that rebuilds an owned ambiguity over its rewritten alternatives keeps
    /// such a node when they become equal, and the pass after it may read the difference.
    pub(super) fn alternatives(alternatives: BTreeSet<Rc<Self>>) -> Rc<Self> {
        let mut fingerprint = Fingerprint::new(3);
        for alternative in &alternatives {
            fingerprint.write_u64(alternative.fingerprint);
        }
        Rc::new(Self {
            fingerprint: fingerprint.finish(),
            node: PackedNode::Ambiguity(alternatives),
        })
    }

    /// The packed form of an owned tree, sharing nothing.
    pub(super) fn from_parsed(term: &ParsedTerm) -> Rc<Self> {
        crate::stack::guarded(|| match term {
            ParsedTerm::Term(leaf) => Self::leaf(leaf.clone()),
            ParsedTerm::Production {
                production,
                children,
                metadata,
            } => Self::production(
                *production,
                children.iter().map(Self::from_parsed).collect(),
                metadata.clone(),
            ),
            ParsedTerm::InstantiatedProduction {
                production,
                parameters,
                children,
                metadata,
            } => Self::instantiated_production(
                *production,
                parameters.clone(),
                children.iter().map(Self::from_parsed).collect(),
                metadata.clone(),
            ),
            ParsedTerm::Ambiguity(alternatives) => {
                Self::ambiguity(alternatives.iter().map(Self::from_parsed).collect())
            }
        })
    }

    pub(super) fn unpack(&self) -> ParsedTerm {
        crate::stack::guarded(|| {
            measure::bump(Counter::ParserUnpackedNodes);
            match &self.node {
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => ParsedTerm::Production {
                    production: *production,
                    children: children.iter().map(|child| child.unpack()).collect(),
                    metadata: metadata.clone(),
                },
                PackedNode::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                } => ParsedTerm::InstantiatedProduction {
                    production: *production,
                    parameters: parameters.clone(),
                    children: children.iter().map(|child| child.unpack()).collect(),
                    metadata: metadata.clone(),
                },
                PackedNode::Term(term) => ParsedTerm::Term(term.clone()),
                PackedNode::Ambiguity(alternatives) => {
                    ParsedTerm::Ambiguity(alternatives.iter().map(|term| term.unpack()).collect())
                }
            }
        })
    }
}

pub(super) fn cmp_packed_structurally(
    left: &Rc<PackedTerm>,
    right: &Rc<PackedTerm>,
) -> std::cmp::Ordering {
    StructuralOrder::default().cmp(left, right)
}

/// The structural comparisons of packed nodes made so far by one pass, so that each pair of
/// nodes is compared once however many orderings meet it: the order of a pair is a function
/// of the two nodes. A pass that orders the alternatives of every ambiguity of a forest would
/// otherwise compare the shared subforests below them again for each ambiguity above.
#[derive(Default)]
pub(super) struct StructuralOrder {
    pairs: rustc_hash::FxHashMap<(*const PackedTerm, *const PackedTerm), std::cmp::Ordering>,
    /// The alternatives of each compared ambiguity in structural order, so that an ambiguity
    /// compared with many others is sorted once: the order of its alternatives is a function of
    /// the ambiguity.
    alternatives: rustc_hash::FxHashMap<*const PackedTerm, Rc<[Rc<PackedTerm>]>>,
    /// Every node a recorded pair or sorted ambiguity names, kept alive while the records are,
    /// so that no other node takes its address meanwhile.
    nodes: rustc_hash::FxHashMap<*const PackedTerm, Rc<PackedTerm>>,
}

impl StructuralOrder {
    /// The order of [`cmp_packed_structurally`].
    pub(super) fn cmp(
        &mut self,
        left: &Rc<PackedTerm>,
        right: &Rc<PackedTerm>,
    ) -> std::cmp::Ordering {
        compare_packed_structurally(left, right, self)
    }

    /// Whether `left` and `right` are equal as terms, which is `PackedTerm` equality: their
    /// fingerprints agree and the memoized structural order finds them equal.
    pub(super) fn equal(&mut self, left: &Rc<PackedTerm>, right: &Rc<PackedTerm>) -> bool {
        Rc::ptr_eq(left, right)
            || (left.fingerprint == right.fingerprint && self.cmp(left, right).is_eq())
    }

    /// `terms` in the order of [`cmp_packed_structurally`].
    pub(super) fn sorted(&mut self, terms: &BTreeSet<Rc<PackedTerm>>) -> Vec<Rc<PackedTerm>> {
        let mut terms = terms.iter().cloned().collect::<Vec<_>>();
        terms.sort_by(|left, right| self.cmp(left, right));
        terms
    }
}

/// The state one lowering of a sort-inferred forest shares across its passes.
///
/// Its interner holds one node per header over child nodes. Every node a pass builds goes
/// through [`Self::intern`], whose children are session nodes already: a node with an equal
/// header (variant, production, parameters and metadata, all compared in full) over the same
/// child nodes, or an ambiguity over the same alternative nodes, is the node the session already
/// has. A leaf is its own node: `Term` equality ignores annotations, which the lowered term
/// keeps, so two leaves are one node only where the forest shares them. A pass memoized by node
/// address therefore computes its result once per node of the forest and once per node it
/// rebuilds over the same children, however many times it rebuilds it. The table keeps every
/// node it returned alive until the session ends, so no memoized address is reused meanwhile.
#[derive(Default)]
pub(super) struct LoweringSession {
    /// The session's nodes by [`intern_key`]; one bucket holds the nodes of one key.
    nodes: rustc_hash::FxHashMap<u64, Vec<Rc<PackedTerm>>>,
    /// The structural order of session nodes, shared by every pass that orders alternatives.
    pub(super) order: StructuralOrder,
    /// Each node's factored form, shared by every pass that factors ambiguities: factoring is a
    /// function of the node. Each entry keeps its node alive beside its address.
    pub(super) factored: PackedNodeResults,
}

/// The results of a pass for packed nodes by the nodes' addresses, each entry holding its node
/// so that the address is not reused while the entry exists.
pub(super) type PackedNodeResults =
    rustc_hash::FxHashMap<*const PackedTerm, (Rc<PackedTerm>, Rc<PackedTerm>)>;

impl LoweringSession {
    /// The session node with the structure of `term`, whose children or alternatives must be
    /// session nodes: `term` itself when the session has no such node yet.
    pub(super) fn intern(&mut self, term: Rc<PackedTerm>) -> Rc<PackedTerm> {
        let bucket = self.nodes.entry(intern_key(&term)).or_default();
        if let Some(existing) = bucket.iter().find(|existing| {
            Rc::ptr_eq(existing, &term) || same_header_over_same_nodes(&existing.node, &term.node)
        }) {
            return Rc::clone(existing);
        }
        bucket.push(Rc::clone(&term));
        term
    }

    /// The session node of an owned tree as written: an ambiguity of one alternative stays an
    /// ambiguity ([`PackedTerm::alternatives`]), so that unpacking it gives `term` back.
    pub(super) fn intern_parsed(&mut self, term: &ParsedTerm) -> Rc<PackedTerm> {
        crate::stack::guarded(|| {
            let packed = match term {
                ParsedTerm::Term(leaf) => PackedTerm::leaf(leaf.clone()),
                ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                } => PackedTerm::production(
                    *production,
                    children
                        .iter()
                        .map(|child| self.intern_parsed(child))
                        .collect(),
                    metadata.clone(),
                ),
                ParsedTerm::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                } => PackedTerm::instantiated_production(
                    *production,
                    parameters.clone(),
                    children
                        .iter()
                        .map(|child| self.intern_parsed(child))
                        .collect(),
                    metadata.clone(),
                ),
                ParsedTerm::Ambiguity(alternatives) => PackedTerm::alternatives(
                    alternatives
                        .iter()
                        .map(|alternative| self.intern_parsed(alternative))
                        .collect(),
                ),
            };
            self.intern(packed)
        })
    }

    /// The session node of a packed forest, with the forest's sharing: each node of `forest`
    /// is interned once, after its children. A node over unchanged children is itself, so
    /// unpacking the result gives the forest's trees, ambiguity nodes where the forest has them.
    pub(super) fn intern_forest(&mut self, forest: &Rc<PackedTerm>) -> Rc<PackedTerm> {
        let mut interned = rustc_hash::FxHashMap::default();
        self.intern_forest_node(&mut interned, forest)
    }

    fn intern_forest_node(
        &mut self,
        interned: &mut rustc_hash::FxHashMap<*const PackedTerm, Rc<PackedTerm>>,
        term: &Rc<PackedTerm>,
    ) -> Rc<PackedTerm> {
        if let Some(known) = interned.get(&Rc::as_ptr(term)) {
            return Rc::clone(known);
        }
        let node = crate::stack::guarded(|| {
            let mut nodes = |nodes: &[Rc<PackedTerm>]| {
                let interned = nodes
                    .iter()
                    .map(|node| self.intern_forest_node(interned, node))
                    .collect::<Vec<_>>();
                let unchanged = nodes
                    .iter()
                    .zip(&interned)
                    .all(|(node, interned)| Rc::ptr_eq(node, interned));
                (!unchanged).then_some(interned)
            };
            match &term.node {
                PackedNode::Term(_) => Rc::clone(term),
                PackedNode::Production {
                    production,
                    children,
                    metadata,
                } => match nodes(children) {
                    None => Rc::clone(term),
                    Some(children) => {
                        PackedTerm::production(*production, children, metadata.clone())
                    }
                },
                PackedNode::InstantiatedProduction {
                    production,
                    parameters,
                    children,
                    metadata,
                } => match nodes(children) {
                    None => Rc::clone(term),
                    Some(children) => PackedTerm::instantiated_production(
                        *production,
                        parameters.clone(),
                        children,
                        metadata.clone(),
                    ),
                },
                PackedNode::Ambiguity(alternatives) => {
                    let alternatives = alternatives.iter().cloned().collect::<Vec<_>>();
                    match nodes(&alternatives) {
                        None => Rc::clone(term),
                        Some(alternatives) => {
                            PackedTerm::alternatives(alternatives.into_iter().collect())
                        }
                    }
                }
            }
        });
        let node = self.intern(node);
        interned.insert(Rc::as_ptr(term), Rc::clone(&node));
        node
    }
}

/// The key under which [`LoweringSession::intern`] looks a node up: its fingerprint and the
/// identities of its children or alternatives, or a leaf's own identity. Two nodes it makes the
/// same are equal in both, so they share a key, and nodes that differ only in which of several
/// equal leaves they are over (a token repeated through a term, the singleton lists built over
/// each copy) do not share a bucket: the fingerprint alone, which ignores identity, would put
/// every one of them in one bucket and make interning them quadratic in their number.
fn intern_key(term: &Rc<PackedTerm>) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = rustc_hash::FxHasher::default();
    term.fingerprint.hash(&mut hasher);
    match &term.node {
        PackedNode::Term(_) => Rc::as_ptr(term).hash(&mut hasher),
        PackedNode::Production { children, .. }
        | PackedNode::InstantiatedProduction { children, .. } => {
            for child in children {
                Rc::as_ptr(child).hash(&mut hasher);
            }
        }
        PackedNode::Ambiguity(alternatives) => {
            for alternative in alternatives {
                Rc::as_ptr(alternative).hash(&mut hasher);
            }
        }
    }
    hasher.finish()
}

/// Whether two nodes have equal headers (variant, production, parameters, metadata) over the
/// same child nodes, or are ambiguities over the same alternative nodes. Two distinct leaves are
/// never the same node here ([`LoweringSession`]).
fn same_header_over_same_nodes(left: &PackedNode, right: &PackedNode) -> bool {
    let same_nodes = |left: &[Rc<PackedTerm>], right: &[Rc<PackedTerm>]| {
        left.len() == right.len()
            && left
                .iter()
                .zip(right)
                .all(|(left, right)| Rc::ptr_eq(left, right))
    };
    match (left, right) {
        (
            PackedNode::Production {
                production: left_production,
                children: left_children,
                metadata: left_metadata,
            },
            PackedNode::Production {
                production: right_production,
                children: right_children,
                metadata: right_metadata,
            },
        ) => {
            left_production == right_production
                && left_metadata == right_metadata
                && same_nodes(left_children, right_children)
        }
        (
            PackedNode::InstantiatedProduction {
                production: left_production,
                parameters: left_parameters,
                children: left_children,
                metadata: left_metadata,
            },
            PackedNode::InstantiatedProduction {
                production: right_production,
                parameters: right_parameters,
                children: right_children,
                metadata: right_metadata,
            },
        ) => {
            left_production == right_production
                && left_parameters == right_parameters
                && left_metadata == right_metadata
                && same_nodes(left_children, right_children)
        }
        (PackedNode::Ambiguity(left), PackedNode::Ambiguity(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| Rc::ptr_eq(left, right))
        }
        _ => false,
    }
}

fn compare_packed_structurally(
    left: &Rc<PackedTerm>,
    right: &Rc<PackedTerm>,
    order: &mut StructuralOrder,
) -> std::cmp::Ordering {
    fn compare(
        left: &Rc<PackedTerm>,
        right: &Rc<PackedTerm>,
        memo: &mut StructuralOrder,
    ) -> std::cmp::Ordering {
        crate::stack::guarded(|| {
            // Invariant: every memoized pair has a complete structural ordering, and recursion only
            // visits a not-yet-memoized pair before recording both directions.
            use std::cmp::Ordering;

            if Rc::ptr_eq(left, right) {
                return Ordering::Equal;
            }
            let key = (Rc::as_ptr(left), Rc::as_ptr(right));
            if let Some(ordering) = memo.pairs.get(&key) {
                return *ordering;
            }
            let ordering = match (&left.node, &right.node) {
                (
                    PackedNode::Production {
                        production: left_production,
                        children: left_children,
                        metadata: left_metadata,
                    },
                    PackedNode::Production {
                        production: right_production,
                        children: right_children,
                        metadata: right_metadata,
                    },
                ) => left_production
                    .cmp(right_production)
                    .then_with(|| {
                        left_children
                            .iter()
                            .zip(right_children)
                            .map(|(left, right)| compare(left, right, memo))
                            .find(|ordering| !ordering.is_eq())
                            .unwrap_or_else(|| left_children.len().cmp(&right_children.len()))
                    })
                    .then_with(|| left_metadata.cmp(right_metadata)),
                (
                    PackedNode::InstantiatedProduction {
                        production: left_production,
                        parameters: left_parameters,
                        children: left_children,
                        metadata: left_metadata,
                    },
                    PackedNode::InstantiatedProduction {
                        production: right_production,
                        parameters: right_parameters,
                        children: right_children,
                        metadata: right_metadata,
                    },
                ) => left_production
                    .cmp(right_production)
                    .then_with(|| left_parameters.cmp(right_parameters))
                    .then_with(|| {
                        left_children
                            .iter()
                            .zip(right_children)
                            .map(|(left, right)| compare(left, right, memo))
                            .find(|ordering| !ordering.is_eq())
                            .unwrap_or_else(|| left_children.len().cmp(&right_children.len()))
                    })
                    .then_with(|| left_metadata.cmp(right_metadata)),
                (PackedNode::Production { .. }, _) => Ordering::Less,
                (_, PackedNode::Production { .. }) => Ordering::Greater,
                (PackedNode::InstantiatedProduction { .. }, _) => Ordering::Less,
                (_, PackedNode::InstantiatedProduction { .. }) => Ordering::Greater,
                (PackedNode::Term(left), PackedNode::Term(right)) => left.cmp(right),
                (PackedNode::Term(_), PackedNode::Ambiguity(_)) => Ordering::Less,
                (PackedNode::Ambiguity(_), PackedNode::Term(_)) => Ordering::Greater,
                (PackedNode::Ambiguity(_), PackedNode::Ambiguity(_)) => {
                    let left = sorted_alternatives(left, memo);
                    let right = sorted_alternatives(right, memo);
                    left.iter()
                        .zip(right.iter())
                        .map(|(left, right)| compare(left, right, memo))
                        .find(|ordering| !ordering.is_eq())
                        .unwrap_or_else(|| left.len().cmp(&right.len()))
                }
            };
            memo.pairs.insert(key, ordering);
            memo.pairs.insert((key.1, key.0), ordering.reverse());
            memo.nodes.entry(key.0).or_insert_with(|| Rc::clone(left));
            memo.nodes.entry(key.1).or_insert_with(|| Rc::clone(right));
            ordering
        })
    }

    /// The alternatives of `ambiguity` in structural order, sorted once per memo.
    fn sorted_alternatives(
        ambiguity: &Rc<PackedTerm>,
        memo: &mut StructuralOrder,
    ) -> Rc<[Rc<PackedTerm>]> {
        let identity = Rc::as_ptr(ambiguity);
        if let Some(sorted) = memo.alternatives.get(&identity) {
            return Rc::clone(sorted);
        }
        let PackedNode::Ambiguity(alternatives) = &ambiguity.node else {
            unreachable!("only ambiguities have alternatives to sort")
        };
        let mut sorted = alternatives.iter().cloned().collect::<Vec<_>>();
        sorted.sort_by(|left, right| compare(left, right, memo));
        let sorted = Rc::<[Rc<PackedTerm>]>::from(sorted);
        memo.alternatives.insert(identity, Rc::clone(&sorted));
        memo.nodes
            .entry(identity)
            .or_insert_with(|| Rc::clone(ambiguity));
        sorted
    }

    compare(left, right, order)
}

pub(super) fn packed_terms_in_structural_order(
    terms: &BTreeSet<Rc<PackedTerm>>,
) -> Vec<Rc<PackedTerm>> {
    StructuralOrder::default().sorted(terms)
}

pub(super) fn packed_variable_names(root: &Rc<PackedTerm>) -> BTreeSet<String> {
    let _span = measure::algorithm_span(Algorithm::ParserDisambiguationReserveNames);
    let mut names = BTreeSet::new();
    let mut visited = HashSet::new();
    let mut pending = vec![Rc::clone(root)];
    // Invariant: `visited` contains exactly the DAG nodes already scanned and `pending` contains
    // reachable nodes whose children or alternatives have not yet been scheduled.
    while let Some(term) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&term)) {
            continue;
        }
        match &term.node {
            PackedNode::InstantiatedProduction { .. } => {
                unreachable!("instantiated productions are created after variable reservation")
            }
            PackedNode::Term(term) => {
                if let Term::Variable { name, .. } = term.unannotated() {
                    names.insert(name.clone());
                }
            }
            PackedNode::Production { children, .. } => {
                pending.extend(children.iter().cloned());
            }
            PackedNode::Ambiguity(alternatives) => {
                pending.extend(alternatives.iter().cloned());
            }
        }
    }
    names
}

struct Fingerprint(u64);

impl Fingerprint {
    const OFFSET: u64 = 0xcbf29ce484222325;
    const PRIME: u64 = 0x100000001b3;

    fn new(kind: u8) -> Self {
        let mut fingerprint = Self(Self::OFFSET);
        fingerprint.write(&[kind]);
        fingerprint
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(Self::PRIME);
        }
    }

    fn write_u64(&mut self, value: u64) {
        self.write(&value.to_le_bytes());
    }

    fn write_usize(&mut self, value: usize) {
        self.write_u64(value as u64);
    }

    fn write_metadata(&mut self, metadata: &TermMetadata) {
        if let Some(span) = metadata.span {
            self.write(&[1]);
            self.write_usize(span.source.0);
            self.write_usize(span.start);
            self.write_usize(span.end);
        }
        if let Some(production) = metadata.production {
            self.write(&[2]);
            self.write(production.as_bytes());
        }
        if let Some(sort) = &metadata.sort {
            self.write(&[3]);
            self.write(sort.to_string().as_bytes());
        }
        // Chart-produced metadata never carries compiler-origin receipts. Omitting that optional
        // field remains collision-safe because equal fingerprints still compare full metadata.
    }

    fn finish(self) -> u64 {
        self.0
    }
}

#[cfg(test)]
pub(super) fn reset_packed_structural_comparisons() {
    PACKED_STRUCTURAL_COMPARISONS.set(0);
}

#[cfg(test)]
pub(super) fn packed_structural_comparisons() -> usize {
    PACKED_STRUCTURAL_COMPARISONS.get()
}

#[cfg(test)]
pub(super) fn reset_unpacked_nodes() {
    UNPACKED_NODES.set(0);
}

#[cfg(test)]
pub(super) fn unpacked_nodes() -> usize {
    UNPACKED_NODES.get()
}

pub(super) type Derivation = Vec<Rc<PackedTerm>>;

impl ParsedTerm {
    /// Equality that also compares the annotations of leaves, which `==` ignores as `Term`
    /// equality does: the tests check that a pass on the packed form of a tree gives the tree
    /// pass's result in every field the lowered term keeps.
    #[cfg(test)]
    pub(super) fn identical(&self, other: &Self) -> bool {
        crate::stack::guarded(|| match (self, other) {
            (
                Self::Production {
                    production: left_production,
                    children: left_children,
                    metadata: left_metadata,
                },
                Self::Production {
                    production: right_production,
                    children: right_children,
                    metadata: right_metadata,
                },
            ) => {
                left_production == right_production
                    && left_metadata == right_metadata
                    && left_children.len() == right_children.len()
                    && left_children
                        .iter()
                        .zip(right_children)
                        .all(|(left, right)| left.identical(right))
            }
            (
                Self::InstantiatedProduction {
                    production: left_production,
                    parameters: left_parameters,
                    children: left_children,
                    metadata: left_metadata,
                },
                Self::InstantiatedProduction {
                    production: right_production,
                    parameters: right_parameters,
                    children: right_children,
                    metadata: right_metadata,
                },
            ) => {
                left_production == right_production
                    && left_parameters == right_parameters
                    && left_metadata == right_metadata
                    && left_children.len() == right_children.len()
                    && left_children
                        .iter()
                        .zip(right_children)
                        .all(|(left, right)| left.identical(right))
            }
            (Self::Term(left), Self::Term(right)) => left.identical(right),
            (Self::Ambiguity(left), Self::Ambiguity(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right)
                        .all(|(left, right)| left.identical(right))
            }
            _ => false,
        })
    }

    #[cfg(test)]
    pub(super) fn leaf(&self) -> Option<&Term> {
        match self {
            Self::Term(term) => Some(term.unannotated()),
            _ => None,
        }
    }
}

pub(super) fn pack_alternatives(nodes: &BTreeSet<Rc<PackedTerm>>) -> Rc<PackedTerm> {
    if nodes.len() == 1 {
        return Rc::clone(nodes.first().expect("one alternative exists"));
    }
    let mut alternatives = BTreeSet::new();
    for node in nodes {
        match &node.node {
            PackedNode::Ambiguity(nested) => alternatives.extend(nested.iter().cloned()),
            _ => {
                alternatives.insert(Rc::clone(node));
            }
        }
    }
    PackedTerm::ambiguity(alternatives)
}

/// The node of `production` over `children`, whose text is `input[start..end]`
/// (`Chart::text_span`): from the first character of its first token to the last character of
/// its last, without the layout around it. A token production reads that text as its token, so
/// with `syntax Names ::= List{Name, ","}` and `syntax MyToks ::= Names [token]`, `( a , b  )`
/// holds the `MyToks` token `a , b`.
pub(super) fn build_packed_term(
    production_index: usize,
    production: &Production,
    children: &[Rc<PackedTerm>],
    input: &str,
    (start, end): (usize, usize),
    provenance: ParseProvenance,
) -> Rc<PackedTerm> {
    if production.token {
        if production.result.is_frontend(FrontendSort::KVariable) {
            return PackedTerm::leaf(
                Term::Variable {
                    name: input[start..end].to_owned(),
                    sort: None,
                }
                .with_metadata(term_metadata(
                    production,
                    provenance.source,
                    provenance.base_offset + start,
                    provenance.base_offset + end,
                )),
            );
        }
        let token = &input[start..end];
        // A MINT.literal token spells its width in the digits after its first `p`/`P`, so
        // `0p32` is an `MInt{32}` whichever declared instantiation scanned it; the metadata
        // still names the scanning production.
        let sort = if production.is_mint_literal() {
            mint_literal_sort(&production.result, token)
        } else {
            production.result.clone()
        };
        return PackedTerm::leaf(
            Term::Token {
                token: token.to_owned(),
                sort,
            }
            .with_metadata(term_metadata(
                production,
                provenance.source,
                provenance.base_offset + start,
                provenance.base_offset + end,
            )),
        );
    }
    if production.record.is_none()
        && !production.bracket
        && (production.transparent || production.label.is_none())
        && let [child] = children
    {
        return Rc::clone(child);
    }
    PackedTerm::production(
        production.term_production.unwrap_or(production_index),
        children.to_vec(),
        term_metadata(
            production,
            provenance.source,
            provenance.base_offset + start,
            provenance.base_offset + end,
        ),
    )
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::kast::ProductionIdentity;

    #[derive(Clone, Debug)]
    enum TestTree {
        Leaf(u8),
        Production(u8, Vec<TestTree>),
        Ambiguity(Vec<TestTree>),
    }

    fn test_tree() -> impl Strategy<Value = TestTree> {
        (0u8..6)
            .prop_map(TestTree::Leaf)
            .prop_recursive(4, 48, 4, |inner| {
                prop_oneof![
                    (0u8..4, prop::collection::vec(inner.clone(), 0..4)).prop_map(
                        |(production, children)| TestTree::Production(production, children)
                    ),
                    prop::collection::vec(inner, 0..4).prop_map(TestTree::Ambiguity),
                ]
            })
    }

    fn pack_test_tree(tree: TestTree) -> Rc<PackedTerm> {
        let node = match tree {
            TestTree::Leaf(value) => PackedNode::Term(Term::Variable {
                name: format!("V{value}"),
                sort: None,
            }),
            TestTree::Production(production, children) => PackedNode::Production {
                production: usize::from(production),
                children: children.into_iter().map(pack_test_tree).collect(),
                metadata: TermMetadata::default(),
            },
            TestTree::Ambiguity(alternatives) => {
                PackedNode::Ambiguity(alternatives.into_iter().map(pack_test_tree).collect())
            }
        };
        Rc::new(PackedTerm {
            fingerprint: 0,
            node,
        })
    }

    proptest! {
        #[test]
        fn packed_structural_comparison_is_a_total_order(
            left in test_tree(),
            middle in test_tree(),
            right in test_tree(),
        ) {
            let left = pack_test_tree(left);
            let middle = pack_test_tree(middle);
            let right = pack_test_tree(right);

            for (first, second) in [(&left, &middle), (&middle, &right), (&left, &right)] {
                let ordering = cmp_packed_structurally(first, second);
                prop_assert_eq!(ordering, cmp_packed_structurally(second, first).reverse());
                if first.node != second.node {
                    prop_assert_eq!(ordering, first.cmp(second));
                }
            }
            prop_assert_eq!(cmp_packed_structurally(&left, &left), std::cmp::Ordering::Equal);
            // One order shared by many comparisons reuses its pairs and sorted ambiguities and
            // orders every pair as a fresh one does.
            let mut order = StructuralOrder::default();
            for (first, second) in [
                (&middle, &left),
                (&left, &right),
                (&right, &middle),
                (&left, &middle),
                (&right, &left),
                (&middle, &right),
            ] {
                prop_assert_eq!(order.cmp(first, second), cmp_packed_structurally(first, second));
            }
            if cmp_packed_structurally(&left, &middle).is_le()
                && cmp_packed_structurally(&middle, &right).is_le()
            {
                prop_assert!(cmp_packed_structurally(&left, &right).is_le());
            }

            let shared = Rc::clone(&middle);
            reset_packed_structural_comparisons();
            prop_assert_eq!(
                cmp_packed_structurally(&middle, &shared),
                std::cmp::Ordering::Equal,
            );
            prop_assert_eq!(middle.cmp(&shared), std::cmp::Ordering::Equal);
            prop_assert_eq!(packed_structural_comparisons(), 0);
        }
    }

    /// A parse forest and an owned parse tree of any depth are dropped on a small stack, also
    /// where an ambiguity holds a deep alternative and where a shared node is still referenced
    /// from outside: a chain of 100,000 productions, whose drop glue once recursed per level, is
    /// dropped on a thread of 64 KiB.
    #[test]
    fn forests_and_trees_of_any_depth_are_dropped_on_a_small_stack() {
        const DEPTH: usize = 100_000;
        std::thread::Builder::new()
            .stack_size(64 << 10)
            .spawn(|| {
                let leaf = || Term::Variable {
                    name: "X".into(),
                    sort: None,
                };
                let mut packed = PackedTerm::leaf(leaf());
                let mut shared = None;
                for level in 0..DEPTH {
                    if level == DEPTH / 2 {
                        shared = Some(Rc::clone(&packed));
                    }
                    packed =
                        PackedTerm::production(level % 3, vec![packed], TermMetadata::default());
                }
                let packed =
                    PackedTerm::ambiguity(BTreeSet::from([packed, PackedTerm::leaf(leaf())]));
                drop(packed);
                let shared = shared.expect("the middle node was kept");
                assert_eq!(Rc::strong_count(&shared), 1);
                drop(shared);

                let mut tree = ParsedTerm::Term(leaf());
                for level in 0..DEPTH {
                    tree = ParsedTerm::Production {
                        production: level % 3,
                        children: vec![tree],
                        metadata: TermMetadata::default(),
                    };
                }
                drop(ParsedTerm::Ambiguity(BTreeSet::from([
                    tree,
                    ParsedTerm::Term(leaf()),
                ])));
            })
            .expect("the worker should spawn")
            .join()
            .expect("the forest and the tree should be dropped");
    }

    fn variable(name: &str) -> ParsedTerm {
        ParsedTerm::Term(Term::Variable {
            name: name.to_owned(),
            sort: None,
        })
    }

    fn derivation(term: ParsedTerm) -> Derivation {
        fn pack(term: ParsedTerm) -> Rc<PackedTerm> {
            match term.into_parts() {
                ParsedParts::Term(term) => PackedTerm::leaf(term),
                ParsedParts::Production {
                    production,
                    children,
                    metadata,
                } => PackedTerm::production(
                    production,
                    children.into_iter().map(pack).collect(),
                    metadata,
                ),
                ParsedParts::Ambiguity(alternatives) => {
                    PackedTerm::ambiguity(alternatives.into_iter().map(pack).collect())
                }
                ParsedParts::InstantiatedProduction { .. } => {
                    panic!("forest tests do not construct post-inference productions")
                }
            }
        }
        vec![pack(term)]
    }

    #[test]
    fn comparing_a_shared_packed_node_uses_its_identity() {
        let node = PackedTerm::production(0, Vec::new(), TermMetadata::default());
        let shared = Rc::clone(&node);
        reset_packed_structural_comparisons();

        assert_eq!(node.cmp(&shared), std::cmp::Ordering::Equal);
        assert_eq!(packed_structural_comparisons(), 0);
    }

    #[test]
    fn unequal_deep_packed_nodes_compare_without_walking_their_children() {
        let chain = |name| {
            let ParsedParts::Term(leaf) = variable(name).into_parts() else {
                unreachable!()
            };
            let mut node = PackedTerm::leaf(leaf);
            for production in 0..256 {
                node = PackedTerm::production(production, vec![node], TermMetadata::default());
            }
            node
        };
        let left = chain("left");
        let right = chain("right");
        reset_packed_structural_comparisons();

        assert_ne!(left.cmp(&right), std::cmp::Ordering::Equal);
        assert_eq!(packed_structural_comparisons(), 0);
    }

    #[test]
    fn production_metadata_participates_in_packed_fingerprints() {
        let metadata = |production| TermMetadata {
            production: Some(
                ProductionIdentity::from_hex(&format!("{:032x}", production)).unwrap(),
            ),
            ..TermMetadata::default()
        };
        let left = PackedTerm::production(0, Vec::new(), metadata(1));
        let right = PackedTerm::production(0, Vec::new(), metadata(2));

        assert_ne!(left.fingerprint, right.fingerprint);
        assert_ne!(left, right);
    }

    #[test]
    fn packed_fingerprint_collisions_fall_back_to_complete_structure() {
        let left = derivation(variable("left")).pop().unwrap().node.clone();
        let right = derivation(variable("right")).pop().unwrap().node.clone();
        let left = PackedTerm {
            fingerprint: 0,
            node: left,
        };
        let right = PackedTerm {
            fingerprint: 0,
            node: right,
        };

        assert_ne!(left.cmp(&right), std::cmp::Ordering::Equal);
        assert_ne!(left, right);
    }

    /// Copies of one leaf, equal as terms, are distinct session nodes, as are equal nodes over
    /// different copies (`f(x)` over each); the interner keeps each in its own bucket, so a term
    /// that repeats a token many times is interned in time linear in its size, not quadratic in
    /// the copies.
    #[test]
    fn interning_copies_of_an_equal_leaf_keeps_one_node_per_bucket() {
        let copies = 1000;
        let node = |production: usize, children: Vec<ParsedTerm>| ParsedTerm::Production {
            production,
            children,
            metadata: TermMetadata::default(),
        };
        let tree = (0..copies).fold(variable("x"), |tree, _| {
            node(1, vec![node(0, vec![variable("x")]), tree])
        });
        let mut session = LoweringSession::default();

        let packed = session.intern_parsed(&tree);

        assert_eq!(session.nodes.values().map(Vec::len).max(), Some(1));
        assert_eq!(session.nodes.len(), 3 * copies + 1);
        assert!(packed.unpack() == tree);
    }
}
