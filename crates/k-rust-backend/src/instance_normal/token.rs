//! Instance-normal tokens. Their fields and constructors are private to this module, and
//! [`InstanceNormal::decide`] is the only way `instance_normal.rs` obtains a token: it reads the
//! shape of the term it answers for itself, and the parent supplies only the answers for the
//! term's immediate subterms and the test that excludes a candidate equation. Each constructor
//! checks the shape of the term it vouches for and returns `None` on a mismatch; the
//! equation-head and collection constructors also need a [`NoEquationReaches`] for that term,
//! and [`NoEquationReaches::scan`], its only mint, enumerates the candidate equations itself.
//! So `instance_normal.rs` can neither vouch for an equation-head or collection root without
//! the scan of every equation that could reach it, nor call a constructor on a term other than
//! the one `decide` answers for.

use crate::{
    definition::{BackendDefinition, SelectionComplete},
    rule::{RewriteRule, TermIndex, term_index},
    term::{HeadRole, Term, TermKind, head::Shape},
};

/// Every instance of some term is a normal form of the definition's equations. Zero-sized, so
/// `Option<InstanceNormal>` has the size of a `bool`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct InstanceNormal(());

/// Every immediate subterm of `subject`, an equation-head application or a collection under
/// scan, is instance-normal: the precondition of the scan's syntactic unification test, which
/// reads the subject's equation-head subterms as the values they denote. A claim about the
/// subterms, not about `subject`, so it is not an [`InstanceNormal`] and nothing converts it
/// into one. Minted only by [`InstanceNormal::decide`], from the [`NormalSubterms`] of the
/// subject it scans, and handed to the exclusion test.
#[derive(Clone, Copy, Debug)]
pub(crate) struct NormalArguments<'t> {
    subject: &'t Term,
}

/// Every immediate subterm of `term` is instance-normal: the precondition of every constructor
/// but [`InstanceNormal::of_value`]. A claim about the subterms, not about `term`, so it is not
/// an [`InstanceNormal`] and cannot be returned as one.
struct NormalSubterms<'t> {
    term: &'t Term,
}

/// No equation the definition could apply to an instance of `subject` reaches it. Minted only by
/// [`NoEquationReaches::scan`].
struct NoEquationReaches<'t> {
    subject: &'t Term,
}

impl InstanceNormal {
    /// Whether every instance of `term` is a normal form (the parent module states the rules).
    /// `subterm` answers for each immediate subterm of `term`. `excluded` tests one candidate
    /// equation against the subject its [`NormalArguments`] names, and holds when the equation's
    /// left-hand side cannot match an instance of that subject. An equation-head application or
    /// a collection is instance-normal only when [`NoEquationReaches::scan`] finds every
    /// candidate excluded, in a definition whose equation selection is complete.
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(super) fn decide<'t>(
        definition: &BackendDefinition,
        term: &'t Term,
        subterm: impl FnMut(&Term) -> Option<InstanceNormal>,
        mut excluded: impl FnMut(&RewriteRule, NormalArguments<'t>) -> bool,
    ) -> Option<Self> {
        let mut no_equation_reaches = |subterms: &NormalSubterms<'t>| {
            let arguments = NormalArguments::of(subterms);
            NoEquationReaches::scan(
                definition.equation_selection_complete()?,
                definition,
                subterms.term,
                |rule| excluded(rule, arguments),
            )
        };
        match term.shape() {
            Shape::DomainValue | Shape::Variable => Self::of_value(term),
            Shape::Injection => Self::of_injection(term, NormalSubterms::of(term, subterm)),
            Shape::Application(role) => match role {
                HeadRole::FreeConstructor => {
                    Self::of_free_constructor(term, NormalSubterms::of(term, subterm))
                }
                HeadRole::EquationHead => {
                    let arguments = NormalSubterms::of(term, subterm)?;
                    let reach = no_equation_reaches(&arguments)?;
                    Self::of_equation_head(term, &arguments, reach)
                }
                // A function application is rewritten by evaluation; an uninterpreted
                // application or a macro/alias has no structural normal-form guarantee.
                HeadRole::Function { .. } | HeadRole::Uninterpreted | HeadRole::Residual => None,
            },
            Shape::Collection(_) => {
                let elements = NormalSubterms::of(term, subterm)?;
                let reach = no_equation_reaches(&elements)?;
                Self::of_collection(term, &elements, reach)
            }
            Shape::And => None,
        }
    }

    /// A domain value, or a variable, which ranges over values.
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    fn of_value(term: &Term) -> Option<Self> {
        match term.shape() {
            Shape::DomainValue | Shape::Variable => Some(Self(())),
            Shape::And | Shape::Injection | Shape::Collection(_) | Shape::Application(_) => None,
        }
    }

    /// A sort injection whose operand is instance-normal: no equation is headed by an injection.
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    fn of_injection(term: &Term, inner: Option<NormalSubterms<'_>>) -> Option<Self> {
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
    fn of_free_constructor(term: &Term, arguments: Option<NormalSubterms<'_>>) -> Option<Self> {
        match term.shape() {
            Shape::Application(role) => match role {
                HeadRole::FreeConstructor => arguments
                    .filter(|arguments| arguments.holds_for(term))
                    .map(|_| Self(())),
                HeadRole::EquationHead
                | HeadRole::Function { .. }
                | HeadRole::Uninterpreted
                | HeadRole::Residual => None,
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
    fn of_equation_head(
        term: &Term,
        arguments: &NormalSubterms<'_>,
        reach: NoEquationReaches<'_>,
    ) -> Option<Self> {
        match term.shape() {
            Shape::Application(role) => match role {
                HeadRole::EquationHead => {
                    (arguments.holds_for(term) && reach.subject == term).then_some(Self(()))
                }
                HeadRole::FreeConstructor
                | HeadRole::Function { .. }
                | HeadRole::Uninterpreted
                | HeadRole::Residual => None,
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
    fn of_collection(
        term: &Term,
        elements: &NormalSubterms<'_>,
        reach: NoEquationReaches<'_>,
    ) -> Option<Self> {
        match term.shape() {
            Shape::Collection(_) => {
                (elements.holds_for(term) && reach.subject == term).then_some(Self(()))
            }
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

impl<'t> NormalArguments<'t> {
    fn of(subterms: &NormalSubterms<'t>) -> Self {
        Self {
            subject: subterms.term,
        }
    }

    /// The scanned subject, whose immediate subterms are instance-normal.
    #[must_use]
    pub(crate) fn subject(self) -> &'t Term {
        self.subject
    }

    /// The precondition for `subject`, minted only when `definition` finds every immediate
    /// subterm of `subject` instance-normal, as [`InstanceNormal::decide`] mints it. For the
    /// unit tests of the syntactic unification test and of its oracle, which need it outside a
    /// scan.
    #[cfg(test)]
    pub(crate) fn of_subterms_for_test(
        definition: &BackendDefinition,
        subject: &'t Term,
    ) -> Option<Self> {
        NormalSubterms::of(subject, |subterm| definition.instance_normal(subterm))
            .map(|subterms| Self::of(&subterms))
    }
}

impl<'t> NormalSubterms<'t> {
    /// Asks `subterm` about each immediate subterm of `term`, in order (the arguments; the
    /// operand; each key then its value, then the rest; the heads, then the middle and the
    /// tails; the elements, then the rest; both conjuncts), stopping at the first that is not
    /// instance-normal.
    #[must_use]
    fn of(
        term: &'t Term,
        mut subterm: impl FnMut(&Term) -> Option<InstanceNormal>,
    ) -> Option<Self> {
        every_immediate_subterm(term, |immediate| subterm(immediate).is_some())
            .then_some(Self { term })
    }

    fn holds_for(&self, term: &Term) -> bool {
        self.term == term
    }
}

/// Whether `normal` holds for each immediate subterm of `term`, asked in the order
/// [`NormalSubterms::of`] states, stopping at the first that fails; `true` for a variable or a
/// domain value. Also asked, with a predicate of its own, about the left-hand side of an
/// equation (`instance_normal::patterns::pattern_facts`); it mints no token.
pub(super) fn every_immediate_subterm(term: &Term, mut normal: impl FnMut(&Term) -> bool) -> bool {
    match term.kind() {
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
                && rest
                    .as_ref()
                    .is_none_or(|(middle, tails)| normal(middle) && tails.iter().all(&mut normal))
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().all(&mut normal) && rest.as_ref().is_none_or(&mut normal)
        }
        TermKind::And(left, right) => normal(left) && normal(right),
        TermKind::DomainValue { .. } | TermKind::Variable(_) => true,
    }
}

impl<'t> NoEquationReaches<'t> {
    /// The only mint. Enumerates the candidates itself: the equations equation selection offers
    /// `subject`, which are the function- and simplification-theory equations indexed by
    /// `term_index(subject)` and by `TermIndex::Variable`, and returns `Some` only when
    /// `excluded` holds for every one of them (their left-hand side cannot match an instance of
    /// `subject`). `selection` makes those candidates every term equation of the definition that
    /// could match an application. Under `check-normal-forms`, a `Some` answer is first checked
    /// against every term equation of the definition (`term::head::check`), which panics when one
    /// surely matches `subject` at its root.
    #[must_use]
    fn scan(
        _selection: SelectionComplete,
        definition: &BackendDefinition,
        subject: &'t Term,
        excluded: impl FnMut(&RewriteRule) -> bool,
    ) -> Option<Self> {
        let none_reaches = candidate_equations(definition, subject).all(excluded);
        #[cfg(feature = "check-normal-forms")]
        if none_reaches {
            crate::term::head::check::assert_no_equation_matches(
                definition,
                subject,
                crate::term::head::check::Claim::InstanceNormal,
            );
        }
        none_reaches.then_some(Self { subject })
    }
}

/// The equations equation selection offers `subject`, of every priority: the function- and
/// simplification-theory equations indexed by `term_index(subject)` and by
/// `TermIndex::Variable`. The candidates of [`NoEquationReaches::scan`] and of
/// [`unexcluded_candidates`].
fn candidate_equations<'d>(
    definition: &'d BackendDefinition,
    subject: &Term,
) -> impl Iterator<Item = &'d RewriteRule> {
    let index = term_index(subject);
    let (functions, simplifications) = (
        definition.function_theory(),
        definition.simplification_theory(),
    );
    [
        functions.get(&index),
        functions.get(&TermIndex::Variable),
        simplifications.get(&index),
        simplifications.get(&TermIndex::Variable),
    ]
    .into_iter()
    .flatten()
    .flat_map(|groups| groups.values().flatten().map(AsRef::as_ref))
}

/// The candidate equations (those of [`NoEquationReaches::scan`]) that `excluded` leaves for the
/// equation-head application `subject`: those whose left-hand side may match an instance of it.
/// `None` when `subject` is not an equation-head application, when one of its immediate
/// subterms is not instance-normal (the precondition of `excluded`), or when the definition's
/// equation selection is not complete, so that the candidates would not be every equation that
/// could reach `subject`. An empty list is not an [`InstanceNormal`]: the caller decides what
/// else sets the remaining equations aside.
pub(super) fn unexcluded_candidates<'d, 't>(
    definition: &'d BackendDefinition,
    subject: &'t Term,
    subterm: impl FnMut(&Term) -> Option<InstanceNormal>,
    mut excluded: impl FnMut(&RewriteRule, NormalArguments<'t>) -> bool,
) -> Option<Vec<&'d RewriteRule>> {
    if subject.shape() != Shape::Application(HeadRole::EquationHead) {
        return None;
    }
    definition.equation_selection_complete()?;
    let subterms = NormalSubterms::of(subject, subterm)?;
    let arguments = NormalArguments::of(&subterms);
    Some(
        candidate_equations(definition, subject)
            .filter(|rule| !excluded(rule, arguments))
            .collect(),
    )
}
