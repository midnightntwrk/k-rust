//! One reading of a node of an inferred forest, as a term whose subterms are shared with the
//! other readings that contain them (`Readings::One`).
//!
//! A node of the forest is reached by several edges, and the one-reading terms of its parents
//! all contain its term. Owned terms would copy it into each of them, so the terms of the
//! one-reading nodes of a forest of N nodes would take up to N times its size. A [`OneTerm`] is
//! instead built over its children's `OneTerm`s, as [`lower_term`](super::super::lower_term)
//! builds a term over its children's terms, and shares them: it costs one node per node of the
//! forest. It stands for exactly one [`Term`], its *term* ([`OneTerm::into_term`]), and every
//! question the readings ask of it ([`View`]) has the answer the same question has on that
//! term, so building the term is left to the root's result and the readings an ambiguity
//! report prints.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use rustc_hash::FxHasher;

use crate::kast::{Label, NodeHead, Sort, Term, TermMetadata, TermSpan};

use super::super::{LoweredNode, kstring_token};

/// One reading's term (module documentation): owned, as long as nothing but the edge that
/// carries it holds it, or shared.
///
/// A term is built owned over owned children, as on an owned tree, and kept owned while it
/// passes from a node to its one parent, so a forest without shared nodes builds its terms as
/// owned trees and nothing more. A term is shared (`OneTerm::shared`) before a second holder
/// takes it: the readings kept for a node's other edges, and a set of readings. A node over a
/// shared child is built shared, over its children shared.
#[derive(Clone)]
pub(super) enum OneTerm {
    Owned(Term),
    Shared(Shared),
}

/// A shared node: a term held whole, or a node over shared children.
#[derive(Clone)]
pub(super) struct Shared(Rc<OneNode>);

#[derive(Clone)]
pub(super) struct OneNode {
    shape: Shape,
    /// The annotation of the node's term, as [`Term::with_metadata`] gives it: `None` when the
    /// term is not annotated. A `Shape::Whole` term carries its own annotations, so it has
    /// none here.
    metadata: Option<TermMetadata>,
    /// The hash of the node's term (`View::hash`).
    hash: u64,
}

#[derive(Clone)]
enum Shape {
    /// A term held whole: a leaf of the forest, a joined token, or a subterm of one.
    Whole(Term),
    Rewrite(Shared, Shared),
    As(Shared, Shared),
    /// The items, none of them spliced further: `Term::Sequence` of their terms.
    Sequence(Vec<Shared>),
    Apply(Label, Vec<Shared>),
}

impl OneTerm {
    /// The `OneTerm` of `term`, owned.
    pub(super) fn owned(term: Term) -> Self {
        Self::Owned(term)
    }

    /// The `OneTerm` of `term`, held whole and shared.
    pub(super) fn whole(term: Term) -> Self {
        Self::Shared(Shared::whole(term))
    }

    /// This term, shared: an owned term is moved into a node and held whole.
    pub(super) fn shared(self) -> Self {
        Self::Shared(self.share())
    }

    fn share(self) -> Shared {
        match self {
            Self::Owned(term) => Shared::whole(term),
            Self::Shared(shared) => shared,
        }
    }

    /// The questions about this term.
    pub(super) fn view(&self) -> View<'_> {
        match self {
            Self::Owned(term) => View::Term(term),
            Self::Shared(shared) => View::of(shared),
        }
    }

    /// Whether `self` and `other` are one shared node, and so stand for one term.
    pub(super) fn ptr_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Shared(left), Self::Shared(right)) => Rc::ptr_eq(&left.0, &right.0),
            _ => false,
        }
    }

    /// The hash of the term (`View::hash`), stored in a shared node.
    pub(super) fn hash(&self) -> u64 {
        match self {
            Self::Owned(term) => View::Term(term).hash(),
            Self::Shared(shared) => shared.0.hash,
        }
    }

    /// The arguments of the term (`term_arguments`), each a `OneTerm`: a shared node's children
    /// shared, and copies of the arguments of a term held whole.
    pub(super) fn arguments(&self) -> Vec<OneTerm> {
        let copies = |term: &Term| {
            super::term_arguments(term)
                .into_iter()
                .map(|argument| Self::Owned(argument.clone()))
                .collect()
        };
        match self {
            Self::Owned(term) => copies(term),
            Self::Shared(shared) => match &shared.0.shape {
                Shape::Whole(term) => copies(term),
                Shape::Rewrite(left, right) | Shape::As(left, right) => {
                    vec![Self::Shared(left.clone()), Self::Shared(right.clone())]
                }
                Shape::Sequence(items) | Shape::Apply(_, items) => {
                    items.iter().cloned().map(Self::Shared).collect()
                }
            },
        }
    }

    /// The items the term contributes to a `~>` sequence it is spliced into (`word_items`).
    pub(super) fn word_items(&self) -> Vec<OneTerm> {
        if matches!(self.view().head(), NodeHead::Sequence) {
            self.arguments()
        } else {
            vec![self.clone()]
        }
    }

    /// The term, taken over where nothing else holds a node and copied elsewhere.
    pub(super) fn into_term(self) -> Term {
        match self {
            Self::Owned(term) => term,
            Self::Shared(shared) => shared.into_term(),
        }
    }

    /// The owned terms of `terms` when every one is owned, otherwise all of them shared.
    fn owned_or_shared(terms: Vec<Self>) -> Result<Vec<Term>, Vec<Shared>> {
        if terms.iter().all(|term| matches!(term, Self::Owned(_))) {
            Ok(terms
                .into_iter()
                .map(|term| match term {
                    Self::Owned(term) => term,
                    Self::Shared(_) => unreachable!("every term is owned"),
                })
                .collect())
        } else {
            Err(terms.into_iter().map(Self::share).collect())
        }
    }
}

impl Shared {
    fn whole(term: Term) -> Self {
        let hash = View::Term(&term).hash();
        Self(Rc::new(OneNode {
            shape: Shape::Whole(term),
            metadata: None,
            hash,
        }))
    }

    fn node(shape: Shape) -> Self {
        let children = match &shape {
            Shape::Whole(_) => unreachable!("a whole term is built by Shared::whole"),
            Shape::Rewrite(left, right) | Shape::As(left, right) => vec![left.0.hash, right.0.hash],
            Shape::Sequence(items) | Shape::Apply(_, items) => {
                items.iter().map(|item| item.0.hash).collect()
            }
        };
        let head = match &shape {
            Shape::Rewrite(..) => NodeHead::Rewrite,
            Shape::As(..) => NodeHead::As,
            Shape::Sequence(_) => NodeHead::Sequence,
            Shape::Apply(label, _) => NodeHead::Apply(Cow::Borrowed(label)),
            Shape::Whole(_) => unreachable!("a whole term is built by Shared::whole"),
        };
        let hash = combine(&head, children);
        Self(Rc::new(OneNode {
            shape,
            metadata: None,
            hash,
        }))
    }

    fn into_term(self) -> Term {
        crate::stack::guarded(|| match Rc::try_unwrap(self.0) {
            Ok(node) => node.into_term(),
            Err(shared) => View::Node(&shared, true).to_term(),
        })
    }
}

impl OneNode {
    fn into_term(self) -> Term {
        let term = match self.shape {
            Shape::Whole(term) => return term,
            Shape::Rewrite(left, right) => Term::Rewrite {
                left: Box::new(left.into_term()),
                right: Box::new(right.into_term()),
            },
            Shape::As(pattern, alias) => Term::As {
                pattern: Box::new(pattern.into_term()),
                alias: Box::new(alias.into_term()),
            },
            Shape::Sequence(items) => {
                Term::Sequence(items.into_iter().map(Shared::into_term).collect())
            }
            Shape::Apply(label, arguments) => Term::Apply {
                label,
                arguments: arguments.into_iter().map(Shared::into_term).collect(),
            },
        };
        annotated(term, self.metadata)
    }
}

/// `term` with the annotation `metadata`, a node's own (`OneNode::metadata`).
fn annotated(term: Term, metadata: Option<TermMetadata>) -> Term {
    match metadata {
        Some(metadata) => Term::Annotated {
            term: Box::new(term),
            metadata,
        },
        None => term,
    }
}

/// Each constructor builds the node of the `Term` constructor of the same name: over owned
/// children that term itself, owned, and otherwise a node over the children shared.
impl LoweredNode for OneTerm {
    fn kstring_token(&self) -> Option<&str> {
        match self.view() {
            View::Term(term) => kstring_token(term),
            View::Node(..) => None,
        }
    }

    fn token(token: String, sort: Sort) -> Self {
        Self::Owned(Term::Token { token, sort })
    }

    /// `Term::sequence` splices an item that is a sequence, or a sequence under one
    /// annotation; a node's own annotation is its only one.
    fn sequence(items: Vec<Self>) -> Self {
        let items = match Self::owned_or_shared(items) {
            Ok(items) => return Self::Owned(Term::sequence(items)),
            Err(items) => items,
        };
        let mut flattened = Vec::new();
        for item in items {
            match &item.0.shape {
                Shape::Sequence(nested) => flattened.extend(nested.iter().cloned()),
                Shape::Whole(term) => {
                    let nested = match term {
                        Term::Sequence(nested) => Some(nested),
                        Term::Annotated { term, .. } => match &**term {
                            Term::Sequence(nested) => Some(nested),
                            _ => None,
                        },
                        _ => None,
                    };
                    match nested {
                        Some(nested) => {
                            flattened.extend(nested.iter().map(|item| Shared::whole(item.clone())));
                        }
                        None => flattened.push(item),
                    }
                }
                _ => flattened.push(item),
            }
        }
        Self::Shared(Shared::node(Shape::Sequence(flattened)))
    }

    fn rewrite(left: Self, right: Self) -> Self {
        match Self::owned_or_shared(vec![left, right]) {
            Ok(children) => {
                let [left, right] = <[Term; 2]>::try_from(children)
                    .unwrap_or_else(|_| unreachable!("two children"));
                Self::Owned(<Term as LoweredNode>::rewrite(left, right))
            }
            Err(children) => {
                let [left, right] = <[Shared; 2]>::try_from(children)
                    .unwrap_or_else(|_| unreachable!("two children"));
                Self::Shared(Shared::node(Shape::Rewrite(left, right)))
            }
        }
    }

    fn alias(pattern: Self, alias: Self) -> Self {
        match Self::owned_or_shared(vec![pattern, alias]) {
            Ok(children) => {
                let [pattern, alias] = <[Term; 2]>::try_from(children)
                    .unwrap_or_else(|_| unreachable!("two children"));
                Self::Owned(<Term as LoweredNode>::alias(pattern, alias))
            }
            Err(children) => {
                let [pattern, alias] = <[Shared; 2]>::try_from(children)
                    .unwrap_or_else(|_| unreachable!("two children"));
                Self::Shared(Shared::node(Shape::As(pattern, alias)))
            }
        }
    }

    fn apply(label: Label, arguments: Vec<Self>) -> Self {
        match Self::owned_or_shared(arguments) {
            Ok(arguments) => Self::Owned(Term::Apply { label, arguments }),
            Err(arguments) => Self::Shared(Shared::node(Shape::Apply(label, arguments))),
        }
    }

    /// An owned term is annotated by `Term::with_metadata`; a shared node's annotation is
    /// overlaid with `metadata` as `Term::with_metadata` overlays a term's, the node copied one
    /// level deep when something else holds it.
    fn with_metadata(self, metadata: TermMetadata) -> Self {
        if metadata == TermMetadata::default() {
            return self;
        }
        let shared = match self {
            Self::Owned(term) => return Self::Owned(term.with_metadata(metadata)),
            Self::Shared(shared) => shared,
        };
        let mut node = Rc::try_unwrap(shared.0).unwrap_or_else(|shared| (*shared).clone());
        match &mut node.shape {
            Shape::Whole(term) => {
                let term = std::mem::replace(term, Term::Sequence(Vec::new()));
                return Self::Shared(Shared::whole(term.with_metadata(metadata)));
            }
            _ => match &mut node.metadata {
                Some(existing) => existing.overlay(metadata),
                None => node.metadata = Some(metadata),
            },
        }
        Self::Shared(Shared(Rc::new(node)))
    }
}

/// A term a question is asked of: a [`Term`], or the term of a shared node, with its
/// annotation (`true`) or without it.
#[derive(Clone, Copy)]
pub(super) enum View<'a> {
    Term(&'a Term),
    Node(&'a OneNode, bool),
}

impl<'a> View<'a> {
    /// The view of a shared node's term.
    fn of(shared: &'a Shared) -> Self {
        match &shared.0.shape {
            Shape::Whole(term) => View::Term(term),
            _ => View::Node(&shared.0, true),
        }
    }

    /// The outermost annotation and the term it annotates, `Term::metadata` and the term inside.
    fn peel(self) -> Option<(&'a TermMetadata, View<'a>)> {
        match self {
            View::Term(Term::Annotated { term, metadata }) => Some((metadata, View::Term(term))),
            View::Term(_) | View::Node(_, false) => None,
            View::Node(node, true) => node
                .metadata
                .as_ref()
                .map(|metadata| (metadata, View::Node(node, false))),
        }
    }

    /// `Term::metadata`.
    pub(super) fn metadata(self) -> Option<&'a TermMetadata> {
        self.peel().map(|(metadata, _)| metadata)
    }

    /// `Term::unannotated`.
    fn unannotated(self) -> View<'a> {
        let mut view = self;
        while let Some((_, inner)) = view.peel() {
            view = inner;
        }
        view
    }

    /// The fields the comparison of terms reads besides the children (`NodeHead::of`).
    pub(super) fn head(self) -> NodeHead<'a> {
        match self.unannotated() {
            View::Term(term) => NodeHead::of(term),
            View::Node(node, _) => match &node.shape {
                Shape::Rewrite(..) => NodeHead::Rewrite,
                Shape::As(..) => NodeHead::As,
                Shape::Sequence(_) => NodeHead::Sequence,
                Shape::Apply(label, _) => NodeHead::Apply(Cow::Borrowed(label)),
                Shape::Whole(_) => unreachable!("a whole term is viewed as a term"),
            },
        }
    }

    /// The term itself when it is a [`Term`] (`View::Term`).
    pub(super) fn as_term(self) -> Option<&'a Term> {
        match self {
            View::Term(term) => Some(term),
            View::Node(..) => None,
        }
    }

    /// The arguments of the term (`term_arguments`).
    pub(super) fn arguments(self) -> Vec<View<'a>> {
        match self.unannotated() {
            View::Term(term) => super::term_arguments(term)
                .into_iter()
                .map(View::Term)
                .collect(),
            View::Node(node, _) => match &node.shape {
                Shape::Rewrite(left, right) | Shape::As(left, right) => {
                    vec![View::of(left), View::of(right)]
                }
                Shape::Sequence(items) | Shape::Apply(_, items) => {
                    items.iter().map(View::of).collect()
                }
                Shape::Whole(_) => unreachable!("a whole term is viewed as a term"),
            },
        }
    }

    /// The items the term contributes to a `~>` sequence it is spliced into (`word_items`).
    pub(super) fn word_items(self) -> Vec<View<'a>> {
        if matches!(self.head(), NodeHead::Sequence) {
            self.arguments()
        } else {
            vec![self]
        }
    }

    /// The hash of the term, without its annotations: of its head (`View::head`), its arity and
    /// its arguments' hashes, so terms equal as `Term::cmp` compares them hash alike.
    pub(super) fn hash(self) -> u64 {
        match self {
            View::Node(node, _) => node.hash,
            View::Term(_) => crate::stack::guarded(|| {
                let arguments = self.arguments();
                combine(
                    &self.head(),
                    arguments.into_iter().map(View::hash).collect::<Vec<_>>(),
                )
            }),
        }
    }

    /// `Term::cmp` of the two terms: their heads, then their arguments in order, then their
    /// arities.
    pub(super) fn cmp(self, other: View<'_>) -> Ordering {
        if let (View::Term(left), View::Term(right)) = (self, other) {
            return left.cmp(right);
        }
        if let (View::Node(left, _), View::Node(right, _)) =
            (self.unannotated(), other.unannotated())
            && std::ptr::eq(left, right)
        {
            return Ordering::Equal;
        }
        crate::stack::guarded(|| {
            self.head().cmp(&other.head()).then_with(|| {
                let (left, right) = (self.arguments(), other.arguments());
                left.iter()
                    .zip(&right)
                    .map(|(left, right)| left.cmp(*right))
                    .find(|ordering| ordering.is_ne())
                    .unwrap_or_else(|| left.len().cmp(&right.len()))
            })
        })
    }

    /// `Term::identical` of the two terms: equal with every annotation, layer by layer.
    pub(super) fn identical(self, other: View<'_>) -> bool {
        if let (View::Term(left), View::Term(right)) = (self, other) {
            return left.identical(right);
        }
        if let (View::Node(left, left_annotated), View::Node(right, right_annotated)) =
            (self, other)
            && std::ptr::eq(left, right)
            && left_annotated == right_annotated
        {
            return true;
        }
        crate::stack::guarded(|| match (self.peel(), other.peel()) {
            (Some((left_metadata, left)), Some((right_metadata, right))) => {
                left_metadata.identical(right_metadata) && left.identical(right)
            }
            (Some(_), None) | (None, Some(_)) => false,
            (None, None) => {
                let (left, right) = (self.arguments(), other.arguments());
                self.head() == other.head()
                    && left.len() == right.len()
                    && left
                        .iter()
                        .zip(&right)
                        .all(|(left, right)| left.identical(*right))
            }
        })
    }

    /// The text the term covers: its own span, or that of its arguments (`term_span`).
    pub(super) fn span(self) -> Option<TermSpan> {
        crate::stack::guarded(|| {
            self.metadata()
                .and_then(|metadata| metadata.span)
                .or_else(|| super::cover(self.arguments().into_iter().filter_map(View::span)))
        })
    }

    /// The term, built.
    pub(super) fn to_term(self) -> Term {
        crate::stack::guarded(|| match self {
            View::Term(term) => term.clone(),
            View::Node(node, with_annotation) => {
                let term = match &node.shape {
                    Shape::Whole(term) => return term.clone(),
                    Shape::Rewrite(left, right) => Term::Rewrite {
                        left: Box::new(View::of(left).to_term()),
                        right: Box::new(View::of(right).to_term()),
                    },
                    Shape::As(pattern, alias) => Term::As {
                        pattern: Box::new(View::of(pattern).to_term()),
                        alias: Box::new(View::of(alias).to_term()),
                    },
                    Shape::Sequence(items) => {
                        Term::Sequence(items.iter().map(|item| View::of(item).to_term()).collect())
                    }
                    Shape::Apply(label, arguments) => Term::Apply {
                        label: label.clone(),
                        arguments: arguments
                            .iter()
                            .map(|argument| View::of(argument).to_term())
                            .collect(),
                    },
                };
                if with_annotation {
                    annotated(term, node.metadata.clone())
                } else {
                    term
                }
            }
        })
    }
}

/// The hash of a term of head `head` over arguments of the hashes `arguments`.
fn combine(head: &NodeHead<'_>, arguments: Vec<u64>) -> u64 {
    let mut state = FxHasher::default();
    head.hash(&mut state);
    state.write_usize(arguments.len());
    for argument in arguments {
        state.write_u64(argument);
    }
    state.finish()
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::kast::test_terms::{decorated, varied_fields};
    use crate::provenance::SourceId;

    /// `term`'s shared form built node by node: each node over its children's shared forms,
    /// annotated as the term is; a leaf, and a node under more than one annotation, held whole
    /// (an application without arguments is built owned).
    fn shared(term: &Term) -> OneTerm {
        crate::stack::guarded(|| match term {
            Term::Annotated {
                term: inner,
                metadata,
            } if !matches!(**inner, Term::Annotated { .. }) => {
                if matches!(
                    &**inner,
                    Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. }
                ) {
                    OneTerm::whole(term.clone())
                } else {
                    shared(inner).with_metadata(metadata.clone())
                }
            }
            Term::Rewrite { left, right } => OneTerm::rewrite(shared(left), shared(right)),
            Term::As { pattern, alias } => OneTerm::alias(shared(pattern), shared(alias)),
            // Built as it stands: `OneTerm::sequence` would splice a sequence among the items.
            Term::Sequence(items) => OneTerm::Shared(Shared::node(Shape::Sequence(
                items.iter().map(|item| shared(item).share()).collect(),
            ))),
            Term::Apply { label, arguments } => {
                OneTerm::apply(label.clone(), arguments.iter().map(shared).collect())
            }
            _ => OneTerm::whole(term.clone()),
        })
    }

    /// `varied_fields` terms with a span on some of their nodes.
    fn annotated_terms() -> impl Strategy<Value = Term> {
        (
            varied_fields(),
            prop::collection::vec(prop::option::of(0_usize..8), 1..16),
        )
            .prop_map(|(term, spans)| {
                let mut spans = spans.into_iter().cycle();
                decorated(&term, &mut || {
                    spans.next().flatten().map(|start| TermMetadata {
                        span: Some(TermSpan {
                            source: SourceId(0),
                            start,
                            end: start + 2,
                        }),
                        ..TermMetadata::default()
                    })
                })
            })
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// A term's shared form, built node by node or held whole, stands for the term and
        /// answers each question as the term does: built back, compared (`Term::cmp`,
        /// `Term::identical`) with another term in either form, hashed, and asked for its head,
        /// annotation, arguments, words and span.
        #[test]
        fn a_shared_term_answers_as_its_term(left in annotated_terms(), right in annotated_terms()) {
            let forms = |term: &Term| {
                [OneTerm::owned(term.clone()), OneTerm::whole(term.clone()), shared(term)]
            };
            for (left_form, right_form) in forms(&left).iter().zip(forms(&right).iter().rev()) {
                prop_assert!(left_form.view().to_term().identical(&left));
                prop_assert!(left_form.clone().into_term().identical(&left));
                prop_assert_eq!(left_form.view().cmp(right_form.view()), left.cmp(&right));
                prop_assert_eq!(
                    left_form.view().identical(right_form.view()),
                    left.identical(&right)
                );
                prop_assert!(left_form.view().identical(left_form.view()));
                if left == right {
                    prop_assert_eq!(left_form.hash(), right_form.hash());
                }
                prop_assert_eq!(left_form.view().head(), NodeHead::of(&left));
                prop_assert_eq!(left_form.view().metadata(), left.metadata());
                prop_assert_eq!(left_form.view().span(), super::super::term_span(&left));
                prop_assert_eq!(
                    left_form.view().arguments().len(),
                    super::super::term_arguments(&left).len()
                );
                prop_assert_eq!(
                    super::super::Key::of_view(left_form.view()) == super::super::Key::of(&left),
                    true
                );
                let words = left_form.word_items();
                prop_assert_eq!(words.len(), left_form.view().word_items().len());
                for (word, view) in words.iter().zip(left_form.view().word_items()) {
                    prop_assert!(word.view().identical(view));
                }
            }
            prop_assert_eq!(OneTerm::whole(left.clone()).hash(), shared(&left).hash());
        }

        /// Each `LoweredNode` constructor builds over shared children the node whose term is the
        /// one the `Term` constructor builds over their terms, its annotation overlaid as
        /// `Term::with_metadata` overlays it.
        #[test]
        fn shared_constructors_build_the_terms_of_term_constructors(
            children in prop::collection::vec(annotated_terms(), 0..4),
            kind in 0_u8..4,
            start in prop::option::of(0_usize..8),
            form_kind in 0_u8..3,
        ) {
            let form = |term: &Term| match form_kind {
                0 => OneTerm::owned(term.clone()),
                1 => OneTerm::whole(term.clone()),
                _ => shared(term),
            };
            let metadata = TermMetadata {
                span: start.map(|start| TermSpan {
                    source: SourceId(0),
                    start,
                    end: start + 1,
                }),
                ..TermMetadata::default()
            };
            let label = Label::new("f");
            let (term, one) = match (kind, children.as_slice()) {
                (0, [left, right, ..]) => (
                    <Term as LoweredNode>::rewrite(left.clone(), right.clone()),
                    OneTerm::rewrite(form(left), form(right)),
                ),
                (1, [left, right, ..]) => (
                    <Term as LoweredNode>::alias(left.clone(), right.clone()),
                    OneTerm::alias(form(left), form(right)),
                ),
                (2, _) => (
                    <Term as LoweredNode>::sequence(children.clone()),
                    OneTerm::sequence(children.iter().map(form).collect()),
                ),
                _ => (
                    <Term as LoweredNode>::apply(label.clone(), children.clone()),
                    OneTerm::apply(label, children.iter().map(form).collect()),
                ),
            };
            let term = LoweredNode::with_metadata(term, metadata.clone());
            let one = one.with_metadata(metadata.clone());
            prop_assert!(one.view().to_term().identical(&term));
            // A child already annotated has its annotation overlaid.
            if let Some(child) = children.first() {
                let overlaid = LoweredNode::with_metadata(child.clone(), metadata.clone());
                prop_assert!(form(child).with_metadata(metadata).into_term().identical(&overlaid));
            }
        }
    }

    /// A shared node's term is shared by the terms built over it, not copied into them: a chain
    /// of n one-reading terms, each over the one before it, holds n nodes. Terms over owned
    /// children are owned.
    #[test]
    fn terms_built_over_a_node_share_it() {
        let mut chain = vec![OneTerm::whole(Term::variable("X"))];
        for _ in 0..100 {
            let previous = chain.last().expect("the chain is not empty").clone();
            chain.push(OneTerm::apply(
                Label::new("f"),
                vec![previous, OneTerm::whole(Term::variable("Y"))],
            ));
        }
        for pair in chain.windows(2) {
            assert_shared(&pair[1].arguments()[0], &pair[0]);
        }
        let owned = OneTerm::apply(
            Label::new("f"),
            vec![
                OneTerm::owned(Term::variable("X")),
                OneTerm::owned(Term::variable("Y")),
            ],
        );
        assert!(matches!(owned, OneTerm::Owned(_)));
        let OneTerm::Shared(first) = &chain[0] else {
            panic!("the first term is shared")
        };
        let first = Rc::strong_count(&first.0);
        assert_eq!(
            first, 2,
            "the first node is held by the chain and its one parent"
        );
    }

    fn assert_shared(left: &OneTerm, right: &OneTerm) {
        assert!(left.ptr_eq(right), "the parent copied its child");
    }
}
