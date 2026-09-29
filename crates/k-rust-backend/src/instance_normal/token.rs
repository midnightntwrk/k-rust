//! Instance-normal tokens. Their fields are private to this module, so the scan in
//! `instance_normal.rs` obtains a token only through the constructors here. Each constructor
//! checks the shape of the term it vouches for and returns `None` on a mismatch; the
//! equation-head and collection constructors also need a [`NoEquationReaches`] for that term,
//! and [`NoEquationReaches::scan`], its only mint, enumerates the candidate equations itself.
//! So no path in `instance_normal.rs` can vouch for an equation-head or collection root without
//! scanning every equation that could reach it.

use crate::{
    definition::{BackendDefinition, SelectionComplete},
    rule::{RewriteRule, TermIndex, term_index},
    term::{HeadRole, Term, TermKind, head::Shape},
};

/// Every instance of some term is a normal form of the definition's equations. Zero-sized, so
/// `Option<InstanceNormal>` has the size of a `bool`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct InstanceNormal(());

/// Every immediate subterm of `term` is instance-normal: the precondition of every constructor
/// but [`InstanceNormal::of_value`]. A claim about the subterms, not about `term`, so it is not
/// an [`InstanceNormal`] and cannot be returned as one.
pub(super) struct NormalSubterms<'t> {
    term: &'t Term,
}

/// No equation the definition could apply to an instance of `subject` reaches it. Minted only by
/// [`NoEquationReaches::scan`].
pub(crate) struct NoEquationReaches<'t> {
    subject: &'t Term,
}

impl InstanceNormal {
    /// A domain value, or a variable, which ranges over values.
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(super) fn of_value(term: &Term) -> Option<Self> {
        match term.shape() {
            Shape::DomainValue | Shape::Variable => Some(Self(())),
            Shape::And | Shape::Injection | Shape::Collection(_) | Shape::Application(_) => None,
        }
    }

    /// A sort injection whose operand is instance-normal: no equation is headed by an injection.
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(super) fn of_injection(term: &Term, inner: Option<NormalSubterms<'_>>) -> Option<Self> {
        match term.shape() {
            Shape::Injection => inner
                .filter(|inner| inner.holds_for(term))
                .map(|_| Self(())),
            Shape::Variable
            | Shape::And
            | Shape::DomainValue
            | Shape::Collection(_)
            | Shape::Application(_) => None,
        }
    }

    /// A free-constructor application over instance-normal arguments: no equation is headed by
    /// a free constructor.
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(super) fn of_free_constructor(
        term: &Term,
        arguments: Option<NormalSubterms<'_>>,
    ) -> Option<Self> {
        match term.shape() {
            Shape::Application(role) => match role {
                HeadRole::FreeConstructor => arguments
                    .filter(|arguments| arguments.holds_for(term))
                    .map(|_| Self(())),
                HeadRole::EquationHead | HeadRole::Function { .. } | HeadRole::Residual => None,
            },
            Shape::Variable
            | Shape::And
            | Shape::DomainValue
            | Shape::Injection
            | Shape::Collection(_) => None,
        }
    }

    /// An equation-head application over instance-normal arguments that no equation reaches.
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(super) fn of_equation_head(
        term: &Term,
        arguments: Option<NormalSubterms<'_>>,
        reach: NoEquationReaches<'_>,
    ) -> Option<Self> {
        match term.shape() {
            Shape::Application(role) => match role {
                HeadRole::EquationHead => arguments
                    .filter(|arguments| arguments.holds_for(term) && reach.subject == term)
                    .map(|_| Self(())),
                HeadRole::FreeConstructor | HeadRole::Function { .. } | HeadRole::Residual => None,
            },
            Shape::Variable
            | Shape::And
            | Shape::DomainValue
            | Shape::Injection
            | Shape::Collection(_) => None,
        }
    }

    /// A map, list or set over instance-normal elements (keys, values and rest) that no
    /// equation reaches. The collection axioms only identify representations of one collection
    /// value, which matching compares as such.
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(super) fn of_collection(
        term: &Term,
        elements: Option<NormalSubterms<'_>>,
        reach: NoEquationReaches<'_>,
    ) -> Option<Self> {
        match term.shape() {
            Shape::Collection(_) => elements
                .filter(|elements| elements.holds_for(term) && reach.subject == term)
                .map(|_| Self(())),
            Shape::Variable
            | Shape::And
            | Shape::DomainValue
            | Shape::Injection
            | Shape::Application(_) => None,
        }
    }

    /// A subterm of an instance-normal term is instance-normal: a normal form's subterms are
    /// normal forms, on every instance.
    #[must_use]
    pub(crate) fn argument(self) -> Self {
        self
    }
}

impl<'t> NormalSubterms<'t> {
    /// Asks `subterm` about each immediate subterm of `term`, in order (the arguments; the
    /// operand; each key then its value, then the rest; the heads, then the middle and the
    /// tails; the elements, then the rest; both conjuncts), stopping at the first that is not
    /// instance-normal.
    #[must_use]
    pub(super) fn of(
        term: &'t Term,
        mut subterm: impl FnMut(&Term) -> Option<InstanceNormal>,
    ) -> Option<Self> {
        let mut normal = |term: &Term| subterm(term).is_some();
        let all = match term.kind() {
            TermKind::Application { arguments, .. } => arguments.iter().all(&mut normal),
            TermKind::Injection { term, .. } => normal(term),
            TermKind::Map { entries, rest, .. } => {
                entries
                    .iter()
                    .all(|(key, value)| normal(key) && normal(value))
                    && rest.as_ref().is_none_or(&mut normal)
            }
            TermKind::List { heads, rest, .. } => {
                heads.iter().all(&mut normal)
                    && rest.as_ref().is_none_or(|(middle, tails)| {
                        normal(middle) && tails.iter().all(&mut normal)
                    })
            }
            TermKind::Set { elements, rest, .. } => {
                elements.iter().all(&mut normal) && rest.as_ref().is_none_or(&mut normal)
            }
            TermKind::And(left, right) => normal(left) && normal(right),
            TermKind::DomainValue { .. } | TermKind::Variable(_) => true,
        };
        all.then_some(Self { term })
    }

    /// The token of the term's subterms, every one of which is instance-normal. A claim about
    /// the subterms, never about the term itself.
    #[must_use]
    pub(super) fn subterm(&self) -> InstanceNormal {
        InstanceNormal(())
    }

    fn holds_for(&self, term: &Term) -> bool {
        self.term == term
    }
}

impl<'t> NoEquationReaches<'t> {
    /// The only mint. Enumerates the candidates itself: the equations equation selection offers
    /// `subject`, which are the function- and simplification-theory equations indexed by
    /// `term_index(subject)` and by `TermIndex::Variable`, and returns `Some` only when
    /// `excluded` holds for every one of them (their left-hand side cannot match an instance of
    /// `subject`). `selection` makes those candidates every term equation of the definition that
    /// could match an application.
    #[must_use]
    pub(super) fn scan(
        _selection: SelectionComplete,
        definition: &BackendDefinition,
        subject: &'t Term,
        mut excluded: impl FnMut(&RewriteRule) -> bool,
    ) -> Option<Self> {
        let indices = [term_index(subject), TermIndex::Variable];
        [
            definition.function_theory(),
            definition.simplification_theory(),
        ]
        .into_iter()
        .all(|theory| {
            indices.iter().all(|index| {
                theory
                    .get(index)
                    .is_none_or(|groups| groups.values().flatten().all(|rule| excluded(rule)))
            })
        })
        .then_some(Self { subject })
    }
}
