//! ```toml algorithm
//! id = "parser.forest.pack"
//! name = "packed parse-forest construction"
//! sites = ["build_packed_term", "pack_alternatives", "append_nodes", "PackedTerm::unpack"]
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
//! sites = ["cmp_packed_structurally", "packed_terms_in_structural_order", "PackedTerm::cmp"]
//! variable = "N = compared subtree nodes when fingerprints tie; P = distinct node pairs reached by one structural comparison; A = alternatives of one compared ambiguity; n = terms in the ordered set"
//! counters = ["ParserPackedStructuralComparisons"]
//!
//! [[cost]]
//! mode = "PackedTerm::cmp"
//! bound = "O(1) unless the fingerprints tie, then O(N)"
//!
//! [[cost]]
//! mode = "cmp_packed_structurally"
//! bound = "O(P x A log A)"
//!
//! [[cost]]
//! mode = "packed_terms_in_structural_order"
//! bound = "O(n log n) structural comparisons, each with a fresh pair memo"
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

use super::chart::Derivations;
#[cfg(test)]
use super::{PACKED_STRUCTURAL_COMPARISONS, UNPACKED_NODES};
use super::{ParseProvenance, Production, mint_literal_sort, term_metadata};

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
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
            self.node.cmp(&other.node)
        })
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
        match term {
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
        }
    }

    pub(super) fn unpack(&self) -> ParsedTerm {
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
    }
}

pub(super) fn cmp_packed_structurally(
    left: &Rc<PackedTerm>,
    right: &Rc<PackedTerm>,
) -> std::cmp::Ordering {
    fn compare(
        left: &Rc<PackedTerm>,
        right: &Rc<PackedTerm>,
        memo: &mut std::collections::HashMap<
            (*const PackedTerm, *const PackedTerm),
            std::cmp::Ordering,
        >,
    ) -> std::cmp::Ordering {
        // Invariant: every memoized pair has a complete structural ordering, and recursion only
        // visits a not-yet-memoized pair before recording both directions.
        use std::cmp::Ordering;

        if Rc::ptr_eq(left, right) {
            return Ordering::Equal;
        }
        let key = (Rc::as_ptr(left), Rc::as_ptr(right));
        if let Some(ordering) = memo.get(&key) {
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
            (PackedNode::Ambiguity(left), PackedNode::Ambiguity(right)) => {
                let mut left = left.iter().cloned().collect::<Vec<_>>();
                let mut right = right.iter().cloned().collect::<Vec<_>>();
                left.sort_by(|left, right| compare(left, right, memo));
                right.sort_by(|left, right| compare(left, right, memo));
                left.iter()
                    .zip(&right)
                    .map(|(left, right)| compare(left, right, memo))
                    .find(|ordering| !ordering.is_eq())
                    .unwrap_or_else(|| left.len().cmp(&right.len()))
            }
        };
        memo.insert(key, ordering);
        memo.insert((key.1, key.0), ordering.reverse());
        ordering
    }

    compare(left, right, &mut std::collections::HashMap::new())
}

pub(super) fn packed_terms_in_structural_order(
    terms: &BTreeSet<Rc<PackedTerm>>,
) -> Vec<Rc<PackedTerm>> {
    let mut terms = terms.iter().cloned().collect::<Vec<_>>();
    terms.sort_by(cmp_packed_structurally);
    terms
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

pub(super) fn append_nodes(
    derivations: &Derivations,
    nodes: &BTreeSet<Rc<PackedTerm>>,
) -> BTreeSet<Derivation> {
    let node = (!nodes.is_empty()).then(|| pack_alternatives(nodes));
    derivations
        .iter()
        .filter_map(|derivation| {
            let mut combined = derivation.clone();
            combined.push(node.clone()?);
            Some(combined)
        })
        .collect()
}

pub(super) fn build_packed_term(
    production_index: usize,
    production: &Production,
    children: &[Rc<PackedTerm>],
    input: &str,
    start: usize,
    end: usize,
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
        // EarleyParser substitutes the digits after the first `p`/`P` of a MINT.literal token
        // into the parametric production, so `0p32` is an `MInt{32}` whichever declared
        // instantiation scanned it; the metadata still names the scanning production.
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

    fn variable(name: &str) -> ParsedTerm {
        ParsedTerm::Term(Term::Variable {
            name: name.to_owned(),
            sort: None,
        })
    }

    fn derivation(term: ParsedTerm) -> Derivation {
        fn pack(term: ParsedTerm) -> Rc<PackedTerm> {
            match term {
                ParsedTerm::Term(term) => PackedTerm::leaf(term),
                ParsedTerm::Production {
                    production,
                    children,
                    metadata,
                } => PackedTerm::production(
                    production,
                    children.into_iter().map(pack).collect(),
                    metadata,
                ),
                ParsedTerm::Ambiguity(alternatives) => {
                    PackedTerm::ambiguity(alternatives.into_iter().map(pack).collect())
                }
                ParsedTerm::InstantiatedProduction { .. } => {
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
            let ParsedTerm::Term(leaf) = variable(name) else {
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
        let PackedTerm { node: left, .. } =
            Rc::unwrap_or_clone(derivation(variable("left")).pop().unwrap());
        let PackedTerm { node: right, .. } =
            Rc::unwrap_or_clone(derivation(variable("right")).pop().unwrap());
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
}
