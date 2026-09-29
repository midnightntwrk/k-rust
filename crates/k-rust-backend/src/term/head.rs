//! Whether the root of a term is the root of every value the term denotes.
//!
//! A backend term denotes a value of the definition's model. A domain value, a sort injection,
//! an internal collection and an application of a free constructor are values whose root is
//! fixed by the term. An application of an equation head (an `anywhere` production that is not a
//! declared function) denotes the value of its normal form under the definition's equations, and
//! distinct normal forms are distinct values, so its root is the root of its value only when the
//! application is a normal form on every instance. A function application denotes whatever its
//! equations and hook make it, a variable ranges over values, and a macro or alias application
//! denotes a value preprocessing should have replaced.
//!
//! An algorithm may refute two terms because their roots differ, replace an equation between two
//! terms by equations between their arguments, fail an occurs check, or prune a rule by a
//! subject's root only when each root involved is fixed. Replacing an equation between two
//! applications of one symbol by equations between their arguments needs, in addition, that the
//! symbol carries no `assoc` or `idem` axiom: those axioms reassociate or collapse the arguments
//! of one value.
//!
//! The classifier has two entry points. `classify_pattern` reads a left-hand side under a
//! `PatternReading` and never consults evidence. `classify_value` reads a subject or operand as
//! the value it denotes, and fixes an equation-head root only with a [`NormalEvidence`] from the
//! oracle its caller names (`NormalForms`). Evidence that an equation-head application is a
//! normal form on every instance comes only from:
//!
//! - an equation scan that found no equation of the definition whose left-hand side may match an
//!   instance, in a definition whose equation selection reaches every term equation (the
//!   instance-normal token of `BackendDefinition::instance_normal`);
//! - the simplifier's certificate, the `evaluated` mark;
//! - being a subterm of an application for which one of those holds;
//! - being the application an equation is tried on, whose root the equation rewrites as written.
//!
//! Syntactic shape (groundness, head kinds, `Term::concrete_after_normalization`, the declared
//! `injective` attribute) is never evidence.
//!
//! The decisive outcomes carry witnesses built here: [`HeadClash`] (two terms whose roots
//! differ), `Distinct` (two ground terms that denote distinct values) and [`RigidCycle`] (a
//! variable occurring in a term through free constructors and injections only).

use super::{HeadRole, InjectionComparison, Term, TermKind, Variable};
use crate::{
    definition::BackendDefinition,
    instance_normal::{InstanceNormal, NormalArguments},
};

/// How a left-hand side is read. A subject or operand has no reading: it is always read as the
/// value it denotes (`classify_value`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PatternReading {
    /// A rewrite rule's left-hand side, matched as written: an equation-head root is fixed.
    AsWritten,
    /// An equation's left-hand side or an implication pattern: an equation-head subterm denotes
    /// the value of its normal form, which the pattern does not fix.
    UpToEquations,
}

/// The kind of a collection root.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CollectionKind {
    Map,
    List,
    Set,
}

/// The kind of a term's root and, for an application, its symbol's role; no evidence. O(1).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Shape {
    Variable,
    And,
    DomainValue,
    Injection,
    Collection(CollectionKind),
    Application(HeadRole),
}

impl Term {
    /// The kind of this term's root and, for an application, its symbol's role.
    #[inline]
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(crate) fn shape(&self) -> Shape {
        match self.kind() {
            TermKind::Variable(_) => Shape::Variable,
            TermKind::And(..) => Shape::And,
            TermKind::DomainValue { .. } => Shape::DomainValue,
            TermKind::Injection { .. } => Shape::Injection,
            TermKind::Map { .. } => Shape::Collection(CollectionKind::Map),
            TermKind::List { .. } => Shape::Collection(CollectionKind::List),
            TermKind::Set { .. } => Shape::Collection(CollectionKind::Set),
            TermKind::Application { symbol, .. } => {
                Shape::Application(symbol.attributes.head_role())
            }
        }
    }
}

/// Evidence that an equation-head application is a normal form on every instance, so that its
/// root is the root of every value it denotes.
///
/// It is built only inside the backend, from the sources the [module documentation](self)
/// lists; a caller outside the crate can name the type but not build a value:
///
/// ```compile_fail
/// use k_rust_backend::term::head::NormalEvidence;
/// fn evidence() -> Option<NormalEvidence> {
///     Some(NormalEvidence(todo!()))
/// }
/// ```
///
/// ```
/// use k_rust_backend::term::head::NormalEvidence;
/// fn evidence() -> Option<NormalEvidence> {
///     None
/// }
/// ```
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NormalEvidence(Source);

/// Where a [`NormalEvidence`] comes from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Source {
    /// A rewrite rule's left-hand side read as written (`PatternReading::AsWritten`): the rule
    /// applies to a subject only through the root as the pattern writes it. Evidence about a
    /// pattern, never about a value.
    AsWritten,
    /// The application an equation is tried on, or its overload lift: the equation rewrites the
    /// root as it stands.
    Given,
    /// The simplifier's `evaluated` mark on an equation-head application.
    Certified,
    /// An instance-normal token: no equation reaches any instance, or a subterm of such a term.
    InstanceNormal,
    /// The root of the subject the instance-normal scan tries an equation on: the equation's
    /// left-hand side rewrites that root as it stands.
    ScannedSubject,
}

impl NormalEvidence {
    /// The root of the application an equation is tried on, or of its overload lift, which the
    /// equation rewrites as written. One call site: the matcher's oracle, for a subject among its
    /// given heads, a set with exactly two insertion points (the equation root and the overload
    /// lift).
    #[cfg_attr(
        not(test),
        expect(dead_code, reason = "first read by the matcher's oracle (CBC-02-T4)")
    )]
    #[must_use]
    pub(crate) fn given() -> Self {
        Self(Source::Given)
    }

    /// The simplifier's certificate: `Some` exactly for an equation-head application that
    /// carries the `evaluated` mark (`Term::with_evaluated_cache`).
    #[must_use]
    pub(crate) fn certified(term: &Term) -> Option<Self> {
        (term.shape() == Shape::Application(HeadRole::EquationHead) && term.attributes().evaluated)
            .then_some(Self(Source::Certified))
    }

    /// An instance-normal token: the term, or a term it is a subterm of, is a normal form on
    /// every instance. The token is zero-sized and names no term, so the caller passes only the
    /// token `BackendDefinition::instance_normal` returned for the classified application or for
    /// a term it is a subterm of.
    #[must_use]
    pub(crate) fn instance_normal(_token: InstanceNormal) -> Self {
        Self(Source::InstanceNormal)
    }
}

/// Where the evidence for an equation-head root read as a value comes from. Each consumer names
/// its oracle, so an intended difference between algorithms is visible at the call site.
pub(crate) trait NormalForms {
    /// Evidence that `application`, an equation-head application, is a normal form on every
    /// instance, or `None`. Asked by `classify_value` only for an equation-head root, once.
    fn evidence(&mut self, application: &Term) -> Option<NormalEvidence>;
}

/// No evidence: every equation-head root read as a value is open (builtin equality).
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "first read by builtin equality (CBC-02-T5)")
)]
pub(crate) struct NoEvidence;

impl NormalForms for NoEvidence {
    fn evidence(&mut self, _application: &Term) -> Option<NormalEvidence> {
        None
    }
}

/// The simplifier's certificate only (structural distinctness).
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "first read by structural distinctness (CBC-02-T5)"
    )
)]
pub(crate) struct CertifiedOnly;

impl NormalForms for CertifiedOnly {
    fn evidence(&mut self, application: &Term) -> Option<NormalEvidence> {
        NormalEvidence::certified(application)
    }
}

/// The instance-normal scan of the definition only (unification).
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "first read by the unifier (CBC-02-T4)")
)]
pub(crate) struct Scanned<'d>(pub &'d BackendDefinition);

impl NormalForms for Scanned<'_> {
    fn evidence(&mut self, application: &Term) -> Option<NormalEvidence> {
        self.0
            .instance_normal(application)
            .map(NormalEvidence::instance_normal)
    }
}

/// The certificate, then the instance-normal scan (the rule index's top key).
pub(crate) struct CertifiedOrScanned<'d>(pub &'d BackendDefinition);

impl NormalForms for CertifiedOrScanned<'_> {
    fn evidence(&mut self, application: &Term) -> Option<NormalEvidence> {
        NormalEvidence::certified(application).or_else(|| {
            self.0
                .instance_normal(application)
                .map(NormalEvidence::instance_normal)
        })
    }
}

/// The subject side of the instance-normal scan's syntactic unification test: holds the
/// precondition that every immediate subterm of the scanned subject is instance-normal, and
/// answers for every equation-head application met on that side, which is the subject or one of
/// its subterms. The subject's own root is the root the scanned equation is tried on, which the
/// equation's left-hand side rewrites as it stands; a proper subterm of the subject lies inside
/// an instance-normal immediate subterm, hence is instance-normal. Built only from a
/// [`NormalArguments`], which only the scan mints; it holds no [`InstanceNormal`].
pub(crate) struct InheritedFromArguments<'t>(pub NormalArguments<'t>);

impl NormalForms for InheritedFromArguments<'_> {
    fn evidence(&mut self, application: &Term) -> Option<NormalEvidence> {
        // A proper subterm is never the same handle as the term that contains it.
        Some(NormalEvidence(if application.ptr_eq(self.0.subject()) {
            Source::ScannedSubject
        } else {
            Source::InstanceNormal
        }))
    }
}

/// A root that is the root of every value its term denotes. Built only by the two classifier
/// entry points.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Fixed<'t> {
    term: &'t Term,
    root: FixedRoot,
}

impl<'t> Fixed<'t> {
    /// The classified term.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "first read by the matcher and the unifier (CBC-02-T4)"
        )
    )]
    #[must_use]
    pub(crate) fn term(self) -> &'t Term {
        self.term
    }

    /// The kind of the fixed root.
    #[must_use]
    pub(crate) fn root(self) -> FixedRoot {
        self.root
    }
}

/// The kind of a fixed root.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FixedRoot {
    DomainValue,
    Injection,
    Collection(CollectionKind),
    FreeConstructor,
    /// An equation-head application with evidence that it is a normal form on every instance,
    /// or a left-hand side read as written.
    EquationHead(NormalEvidence),
}

/// A root that does not fix the root of the values its term denotes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Open {
    Variable,
    And,
    /// A function application; `injective` is the role's declared injectivity (never set for a
    /// symbol with `anywhere` equations).
    Function {
        injective: bool,
    },
    /// An equation head read up to equations, or read as a value without evidence.
    EquationHead,
}

/// The classification of a root.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Head<'t> {
    Fixed(Fixed<'t>),
    Open(
        #[cfg_attr(
            not(test),
            expect(
                dead_code,
                reason = "first read by the matcher and the unifier (CBC-02-T4)"
            )
        )]
        Open,
    ),
    /// A macro or alias application: preprocessing should have replaced it, so its value is not
    /// described by the definition. Each consumer decides it in an arm of its own.
    Residual,
}

/// Classify a left-hand side under `reading`. Never consults evidence: an equation-head root is
/// fixed as written ([`PatternReading::AsWritten`]) or open up to equations
/// ([`PatternReading::UpToEquations`]).
#[inline]
#[must_use]
#[deny(clippy::wildcard_enum_match_arm)]
pub(crate) fn classify_pattern(reading: PatternReading, term: &Term) -> Head<'_> {
    classify(term, || match reading {
        PatternReading::AsWritten => Some(NormalEvidence(Source::AsWritten)),
        PatternReading::UpToEquations => None,
    })
}

/// Classify a subject or operand as the value it denotes. Asks `normal` for evidence only for an
/// equation-head root, and only once. Evidence of a left-hand side's reading
/// ([`PatternReading::AsWritten`]) says nothing about a value, so an oracle that hands it back
/// leaves the root open.
#[inline]
#[must_use]
#[deny(clippy::wildcard_enum_match_arm)]
pub(crate) fn classify_value<'t, N: NormalForms + ?Sized>(
    term: &'t Term,
    normal: &mut N,
) -> Head<'t> {
    classify(term, || {
        let evidence = normal.evidence(term);
        debug_assert!(
            evidence.is_none_or(|evidence| evidence.0 != Source::AsWritten),
            "a value is not read as written"
        );
        evidence.filter(|evidence| evidence.0 != Source::AsWritten)
    })
}

/// The one table from a root's shape to its classification; `equation_head` supplies the
/// evidence for an equation-head root.
#[inline]
#[deny(clippy::wildcard_enum_match_arm)]
fn classify(term: &Term, equation_head: impl FnOnce() -> Option<NormalEvidence>) -> Head<'_> {
    let fixed = |root| Head::Fixed(Fixed { term, root });
    match term.shape() {
        Shape::Variable => Head::Open(Open::Variable),
        Shape::And => Head::Open(Open::And),
        Shape::DomainValue => fixed(FixedRoot::DomainValue),
        Shape::Injection => fixed(FixedRoot::Injection),
        Shape::Collection(kind) => fixed(FixedRoot::Collection(kind)),
        Shape::Application(role) => match role {
            HeadRole::FreeConstructor => fixed(FixedRoot::FreeConstructor),
            HeadRole::EquationHead => match equation_head() {
                Some(evidence) => fixed(FixedRoot::EquationHead(evidence)),
                None => Head::Open(Open::EquationHead),
            },
            HeadRole::Function { injective, .. } => Head::Open(Open::Function { injective }),
            HeadRole::Residual => Head::Residual,
        },
    }
}

/// Two fixed roots compared by root alone: the single table of "distinct fixed roots denote
/// distinct values".
#[derive(Clone, Copy, Debug)]
pub(crate) enum RootComparison<'t> {
    /// Different symbols or sort arguments of two applications; an application against a
    /// domain value, an injection or a collection; a domain value against an injection or a
    /// collection; an injection against a collection; two collections of different kinds.
    Distinct(
        #[cfg_attr(
            not(test),
            expect(
                dead_code,
                reason = "first read by the matcher, the unifier and structural distinctness (CBC-02-T4, CBC-02-T5)"
            )
        )]
        RootsDiffer<'t>,
    ),
    /// One symbol without `assoc` or `idem`, equal sort arguments, equal arity: the two values
    /// are equal exactly when the arguments are.
    SameApplication(
        #[cfg_attr(
            not(test),
            expect(
                dead_code,
                reason = "first read by the matcher, the unifier and structural distinctness (CBC-02-T4, CBC-02-T5)"
            )
        )]
        SameApplication<'t>,
    ),
    /// One symbol with `assoc` or `idem`, equal sort arguments, equal arity: the root decides
    /// nothing about the arguments, which the symbol's own axioms reassociate or collapse.
    SameAlgebraicSymbol,
    /// One symbol name and equal sort arguments, different arity: an ill-formed pair.
    ArityMismatch,
    /// Two domain values: compared by sort and value.
    DomainValues,
    /// Two injections: compared by their sorts and operands.
    Injections,
    /// Two collections of one kind: compared as collection values.
    Collections(
        #[cfg_attr(
            not(test),
            expect(dead_code, reason = "first read by the matcher (CBC-02-T4)")
        )]
        CollectionKind,
    ),
}

/// Compare two fixed roots. Each side is matched on its own, so every pair of root kinds is
/// named.
#[must_use]
#[deny(clippy::wildcard_enum_match_arm)]
pub(crate) fn compare_roots<'t>(left: Fixed<'t>, right: Fixed<'t>) -> RootComparison<'t> {
    let differ = RootComparison::Distinct(RootsDiffer {
        left: left.term,
        right: right.term,
    });
    match left.root {
        FixedRoot::DomainValue => match right.root {
            FixedRoot::DomainValue => RootComparison::DomainValues,
            FixedRoot::Injection
            | FixedRoot::Collection(_)
            | FixedRoot::FreeConstructor
            | FixedRoot::EquationHead(_) => differ,
        },
        FixedRoot::Injection => match right.root {
            FixedRoot::Injection => RootComparison::Injections,
            FixedRoot::DomainValue
            | FixedRoot::Collection(_)
            | FixedRoot::FreeConstructor
            | FixedRoot::EquationHead(_) => differ,
        },
        FixedRoot::Collection(kind) => match right.root {
            FixedRoot::Collection(other) if other == kind => RootComparison::Collections(kind),
            FixedRoot::Collection(_)
            | FixedRoot::DomainValue
            | FixedRoot::Injection
            | FixedRoot::FreeConstructor
            | FixedRoot::EquationHead(_) => differ,
        },
        FixedRoot::FreeConstructor | FixedRoot::EquationHead(_) => match right.root {
            FixedRoot::FreeConstructor | FixedRoot::EquationHead(_) => {
                compare_applications(left.term, right.term).unwrap_or(differ)
            }
            FixedRoot::DomainValue | FixedRoot::Injection | FixedRoot::Collection(_) => differ,
        },
    }
}

/// Two applications with fixed roots: `None` when their symbols or sort arguments differ.
fn compare_applications<'t>(left: &'t Term, right: &'t Term) -> Option<RootComparison<'t>> {
    let (
        TermKind::Application {
            symbol: left_symbol,
            sort_arguments: left_sorts,
            arguments: left_arguments,
        },
        TermKind::Application {
            symbol: right_symbol,
            sort_arguments: right_sorts,
            arguments: right_arguments,
        },
    ) = (left.kind(), right.kind())
    else {
        unreachable!("a free-constructor or equation-head root is an application");
    };
    if left_symbol.name != right_symbol.name || left_sorts != right_sorts {
        return None;
    }
    Some(if left_arguments.len() != right_arguments.len() {
        RootComparison::ArityMismatch
    } else if left_symbol.attributes.associative || left_symbol.attributes.idempotent {
        RootComparison::SameAlgebraicSymbol
    } else {
        RootComparison::SameApplication(SameApplication {
            left: left_arguments,
            right: right_arguments,
        })
    })
}

/// Witness that the roots of two classified terms differ. Holds the two borrowed handles.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RootsDiffer<'t> {
    left: &'t Term,
    right: &'t Term,
}

/// The argument slices of two applications of one free symbol with equal sort arguments and
/// arity: the only source of argument pairs for a decomposition by a fixed root.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SameApplication<'t> {
    left: &'t [Term],
    right: &'t [Term],
}

impl<'t> SameApplication<'t> {
    /// The argument pairs, left argument first, in argument order.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "first read by the matcher and the unifier (CBC-02-T4)"
        )
    )]
    pub(crate) fn pairs(self) -> impl Iterator<Item = (&'t Term, &'t Term)> {
        self.left.iter().zip(self.right)
    }
}

/// Two terms whose roots differ, so that no value of one is a value of the other.
///
/// The fields are private and the constructors belong to the backend: a caller outside the
/// crate can read a clash but not build one.
///
/// ```compile_fail
/// use k_rust_backend::term::{Term, head::HeadClash};
/// fn clash(left: Term, right: Term) -> Option<HeadClash> {
///     Some(HeadClash { left, right })
/// }
/// ```
///
/// ```
/// use k_rust_backend::term::{Term, head::HeadClash};
/// fn clash(left: Term, right: Term) -> Option<HeadClash> {
///     let _ = (left, right);
///     None
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeadClash {
    left: Term,
    right: Term,
}

impl HeadClash {
    /// The first term of the clash.
    #[must_use]
    pub fn left(&self) -> &Term {
        &self.left
    }

    /// The second term of the clash.
    #[must_use]
    pub fn right(&self) -> &Term {
        &self.right
    }

    /// The two terms, first then second.
    #[must_use]
    pub fn into_terms(self) -> (Term, Term) {
        (self.left, self.right)
    }

    /// The clash `compare_roots` found between two fixed roots. Moves the owned handles the
    /// caller already holds for the two classified terms.
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "first read by the matcher and the unifier (CBC-02-T4)"
        )
    )]
    #[must_use]
    pub(crate) fn new(witness: RootsDiffer<'_>, left: Term, right: Term) -> Self {
        debug_assert!(
            witness.left.ptr_eq(&left) && witness.right.ptr_eq(&right),
            "a head clash holds the terms its witness compared"
        );
        Self { left, right }
    }

    /// A clash between an application of an overloaded production and another root, in either
    /// order, where the overloaded side is not fixed under its reading. It holds only because an
    /// overloaded production has no equations besides its overload equations, which the backend
    /// does not check (open question Q2 of the classifier's design).
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "first read by the matcher's overload refutations (CBC-02-T4)"
        )
    )]
    #[must_use]
    pub(crate) fn overload_family(left: Term, right: Term) -> Self {
        debug_assert!(
            matches!(left.shape(), Shape::Application(_))
                || matches!(right.shape(), Shape::Application(_)),
            "an overload clash has an application on one side"
        );
        Self { left, right }
    }

    /// A clash between a residual macro or alias root and another root, in either order. A
    /// residual application's value is its unknown expansion, so the clash holds only because
    /// the executable boundary rejects such terms first (open question Q3 of the classifier's
    /// design).
    #[cfg_attr(
        not(test),
        expect(
            dead_code,
            reason = "first read by the matcher's residual refutation (CBC-02-T4)"
        )
    )]
    #[must_use]
    pub(crate) fn residual_root(left: Term, right: Term) -> Self {
        let residual = Shape::Application(HeadRole::Residual);
        debug_assert!(
            left.shape() == residual || right.shape() == residual,
            "a residual clash has a macro or alias root on one side"
        );
        Self { left, right }
    }
}

/// Witness that two ground terms denote distinct values. Zero-sized; minted only here.
#[derive(Debug)]
pub(crate) struct Distinct(());

#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "first read by structural distinctness (CBC-02-T5)"
    )
)]
impl Distinct {
    /// Two fixed roots that differ denote distinct values.
    #[must_use]
    pub(crate) fn of_roots(_witness: RootsDiffer<'_>) -> Self {
        Self(())
    }

    /// Two domain values (`RootComparison::DomainValues`) with different sorts or values.
    #[must_use]
    pub(crate) fn of_domain_values(left: Fixed<'_>, right: Fixed<'_>) -> Option<Self> {
        match (left.term.kind(), right.term.kind()) {
            (
                TermKind::DomainValue {
                    sort: left_sort,
                    value: left_value,
                },
                TermKind::DomainValue {
                    sort: right_sort,
                    value: right_value,
                },
            ) => (left_sort != right_sort || left_value != right_value).then_some(Self(())),
            _ => None,
        }
    }

    /// Two injections the sort graph separates (`InjectionComparison::Distinct`).
    #[must_use]
    #[deny(clippy::wildcard_enum_match_arm)]
    pub(crate) fn of_injection_sorts(comparison: &InjectionComparison) -> Option<Self> {
        match comparison {
            InjectionComparison::Distinct => Some(Self(())),
            InjectionComparison::Compare(..) | InjectionComparison::Undecided => None,
        }
    }

    /// Two applications of one free symbol are distinct when a pair of their arguments is.
    #[must_use]
    pub(crate) fn through_argument(_same: SameApplication<'_>, _argument: Distinct) -> Self {
        Self(())
    }
}

/// `variable` occurs in `term` below at least one free-constructor application or injection,
/// and through such roots only, so `variable = term` has no finite solution. Built only by
/// `rigid_occurrence`; a caller outside the crate can read a cycle but not build one.
///
/// ```compile_fail
/// use k_rust_backend::term::{Term, Variable, head::RigidCycle};
/// fn cycle(variable: Variable, term: Term) -> Option<RigidCycle> {
///     Some(RigidCycle { variable, term })
/// }
/// ```
///
/// ```
/// use k_rust_backend::term::{Term, Variable, head::RigidCycle};
/// fn cycle(variable: Variable, term: Term) -> Option<RigidCycle> {
///     let _ = (variable, term);
///     None
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RigidCycle {
    variable: Variable,
    term: Term,
}

impl RigidCycle {
    /// The variable that occurs in its own binding.
    #[must_use]
    pub fn variable(&self) -> &Variable {
        &self.variable
    }

    /// The term the variable would be bound to.
    #[must_use]
    pub fn term(&self) -> &Term {
        &self.term
    }
}

/// A [`RigidCycle`] when `variable` occurs in `term` below a free-constructor application or an
/// injection, through such roots only. A free constructor and an injection build a value from
/// the values of their arguments, strictly larger than each of them, so no finite value equals
/// a value built around itself. An occurrence under any other root (a function, an equation
/// head, a collection, a conjunction) may disappear when that root is evaluated, and `term`
/// being `variable` itself is no cycle.
#[must_use]
#[deny(clippy::wildcard_enum_match_arm)]
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "first read by the matcher and the unifier (CBC-02-T4)"
    )
)]
pub(crate) fn rigid_occurrence(variable: &Variable, term: &Term) -> Option<RigidCycle> {
    let below = match term.shape() {
        Shape::Injection | Shape::Application(HeadRole::FreeConstructor) => {
            occurs_rigidly(variable, term)
        }
        Shape::Application(
            HeadRole::EquationHead | HeadRole::Function { .. } | HeadRole::Residual,
        )
        | Shape::Variable
        | Shape::And
        | Shape::DomainValue
        | Shape::Collection(_) => false,
    };
    below.then(|| RigidCycle {
        variable: variable.clone(),
        term: term.clone(),
    })
}

/// Whether `variable` is `term` or occurs in it through free-constructor applications and
/// injections only.
#[deny(clippy::wildcard_enum_match_arm)]
fn occurs_rigidly(variable: &Variable, term: &Term) -> bool {
    if !term.attributes().variables.contains(variable) {
        return false;
    }
    match term.kind() {
        TermKind::Variable(found) => found == variable,
        TermKind::Injection { term, .. } => occurs_rigidly(variable, term),
        TermKind::Application {
            symbol, arguments, ..
        } => match symbol.attributes.head_role() {
            HeadRole::FreeConstructor => arguments
                .iter()
                .any(|argument| occurs_rigidly(variable, argument)),
            HeadRole::EquationHead | HeadRole::Function { .. } | HeadRole::Residual => false,
        },
        TermKind::And(..)
        | TermKind::DomainValue { .. }
        | TermKind::Map { .. }
        | TermKind::List { .. }
        | TermKind::Set { .. } => false,
    }
}

/// Whether `term` is a ground term that is a normal form by the mark: concrete after
/// normalization (ground, every root one a normal form can have) and marked `evaluated`, which
/// construction sets on free-constructor applications over marked arguments and the simplifier
/// sets only with its certificate. The one definition of the test.
#[must_use]
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "first read by definedness (CBC-02-T5)")
)]
pub(crate) fn certified_ground_normal_form(term: &Term) -> bool {
    term.concrete_after_normalization() && term.attributes().evaluated
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::term::{FunctionType, Sort, Symbol, SymbolType};

    /// The 18415fba definition: `wrap` is an equation head with the equation `wrap(s(z)) =
    /// wrap(z)` (emitted with an `\in` binder, as kompile emits anywhere rules); it also carries
    /// `injective`, which no reading of it may rely on.
    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                sort SortW{} []
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol s{}(SortNat{}) : SortNat{} [constructor{}(), functional{}(), injective{}()]
                symbol wrap{}(SortNat{}) : SortW{} [anywhere{}(), functional{}(), injective{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(\in{SortNat{}, R}(X0:SortNat{}, s{}(z{}())), \top{R}())
                    ),
                    \equals{SortW{}, R}(
                        wrap{}(X0:SortNat{}),
                        \and{SortW{}}(wrap{}(z{}()), \top{SortW{}}())
                    )
                ) [label{}("collapse"), anywhere{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn internal(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize")
    }

    fn sort() -> Sort {
        Sort::simple("SortS")
    }

    fn variable(name: &str) -> Variable {
        Variable::new(name, sort())
    }

    fn var(name: &str) -> Term {
        Term::variable(variable(name))
    }

    fn symbol(name: &str, arity: usize, build: impl FnOnce(&mut Symbol)) -> Arc<Symbol> {
        let mut symbol = Symbol::constructor(name, vec![sort(); arity], sort());
        build(&mut symbol);
        Arc::new(symbol)
    }

    fn apply(symbol: &Arc<Symbol>, arguments: Vec<Term>) -> Term {
        Term::application(symbol.clone(), Vec::new(), arguments)
    }

    fn function(name: &str, arity: usize) -> Arc<Symbol> {
        symbol(name, arity, |symbol| {
            symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
        })
    }

    fn fixed(head: Head<'_>) -> Fixed<'_> {
        match head {
            Head::Fixed(fixed) => fixed,
            Head::Open(_) | Head::Residual => panic!("expected a fixed root, got {head:?}"),
        }
    }

    fn value(term: &Term) -> Fixed<'_> {
        fixed(classify_value(term, &mut NoEvidence))
    }

    /// Acceptance (18415fba): the subject `wrap(s(X))` has no evidence (the equation `wrap(s(z))
    /// = wrap(z)` rewrites its instance at `X = z`), so its root is open, while the same term as
    /// a rewrite rule's left-hand side is fixed as written.
    #[test]
    fn an_unscanned_equation_head_is_open_as_a_value_and_fixed_as_written() {
        let definition = definition();
        let redex = internal(&definition, "wrap{}(s{}(X:SortNat{}))");
        assert!(matches!(
            classify_value(&redex, &mut Scanned(&definition)),
            Head::Open(Open::EquationHead)
        ));
        let as_written = fixed(classify_pattern(PatternReading::AsWritten, &redex));
        assert!(as_written.term().ptr_eq(&redex));
        assert_eq!(
            as_written.root(),
            FixedRoot::EquationHead(NormalEvidence(Source::AsWritten))
        );
        assert!(matches!(
            classify_pattern(PatternReading::UpToEquations, &redex),
            Head::Open(Open::EquationHead)
        ));
        // No equation reaches an instance of `wrap(s(s(X)))`, so the scan fixes its root.
        let normal = internal(&definition, "wrap{}(s{}(s{}(X:SortNat{})))");
        assert_eq!(
            fixed(classify_value(&normal, &mut Scanned(&definition))).root(),
            FixedRoot::EquationHead(NormalEvidence(Source::InstanceNormal))
        );
    }

    /// Each oracle answers from its own source only.
    #[test]
    fn each_oracle_fixes_an_equation_head_from_its_own_source() {
        let definition = definition();
        let plain = internal(&definition, "wrap{}(z{}())");
        let marked = plain.with_evaluated_cache();
        let redex = internal(&definition, "wrap{}(s{}(z{}()))").with_evaluated_cache();
        let root = |term: &Term, normal: &mut dyn NormalForms| match classify_value(term, normal) {
            Head::Fixed(fixed) => Some(fixed.root()),
            Head::Open(open) => {
                assert_eq!(open, Open::EquationHead);
                None
            }
            Head::Residual => panic!("wrap is no macro"),
        };
        let certified = Some(FixedRoot::EquationHead(NormalEvidence(Source::Certified)));
        let scanned = Some(FixedRoot::EquationHead(NormalEvidence(
            Source::InstanceNormal,
        )));
        assert_eq!(root(&marked, &mut NoEvidence), None);
        assert_eq!(root(&plain, &mut CertifiedOnly), None);
        assert_eq!(root(&marked, &mut CertifiedOnly), certified);
        assert_eq!(root(&plain, &mut Scanned(&definition)), scanned);
        assert_eq!(root(&redex, &mut Scanned(&definition)), None);
        assert_eq!(
            root(&marked, &mut CertifiedOrScanned(&definition)),
            certified
        );
        assert_eq!(root(&plain, &mut CertifiedOrScanned(&definition)), scanned);
        // The scan's subject side answers for its equation heads: the subject's root is the one
        // the equation is tried on, and any other application on that side is a subterm of an
        // instance-normal argument.
        let arguments = NormalArguments::of_subterms_for_test(&definition, &redex)
            .expect("the argument s(z) is instance-normal");
        assert_eq!(
            root(&redex, &mut InheritedFromArguments(arguments)),
            Some(FixedRoot::EquationHead(NormalEvidence(
                Source::ScannedSubject
            )))
        );
        assert_eq!(
            root(&plain, &mut InheritedFromArguments(arguments)),
            scanned
        );
        assert_eq!(NormalEvidence::certified(&plain), None);
        assert_eq!(
            NormalEvidence::certified(&internal(&definition, "s{}(z{}())")),
            None,
            "the mark on a free constructor is structure, not a certificate"
        );
        assert_eq!(NormalEvidence::given(), NormalEvidence(Source::Given));
    }

    /// An oracle cannot turn a pattern's reading into evidence about a value.
    #[test]
    #[cfg_attr(
        debug_assertions,
        should_panic(expected = "a value is not read as written")
    )]
    fn evidence_of_a_reading_does_not_fix_a_value() {
        struct Smuggled(NormalEvidence);
        impl NormalForms for Smuggled {
            fn evidence(&mut self, _application: &Term) -> Option<NormalEvidence> {
                Some(self.0)
            }
        }
        let definition = definition();
        let redex = internal(&definition, "wrap{}(s{}(X:SortNat{}))");
        let FixedRoot::EquationHead(as_written) =
            fixed(classify_pattern(PatternReading::AsWritten, &redex)).root()
        else {
            panic!("an equation head read as written is fixed");
        };
        assert!(matches!(
            classify_value(&redex, &mut Smuggled(as_written)),
            Head::Open(Open::EquationHead)
        ));
    }

    /// Every shape against both entry points.
    #[test]
    fn the_shape_decides_every_root_but_an_equation_head() {
        let constructor = symbol("c", 1, |_| {});
        let injective = symbol("inj", 1, |symbol| {
            symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
            symbol.attributes = symbol.attributes.clone().with_injective(true);
        });
        let residual = symbol("m", 1, |symbol| symbol.attributes.macro_or_alias = true);
        let terms = [
            var("X"),
            Term::and(var("X"), var("Y")),
            Term::domain_value(sort(), "1"),
            Term::injection(Sort::simple("SortSub"), sort(), var("X")),
            apply(&constructor, vec![var("X")]),
            apply(&function("f", 1), vec![var("X")]),
            apply(&injective, vec![var("X")]),
            apply(&residual, vec![var("X")]),
        ];
        let expected = [
            "Open(Variable)",
            "Open(And)",
            "Fixed(DomainValue)",
            "Fixed(Injection)",
            "Fixed(FreeConstructor)",
            "Open(Function { injective: false })",
            "Open(Function { injective: true })",
            "Residual",
        ];
        let describe = |head: Head<'_>| match head {
            Head::Fixed(fixed) => format!("Fixed({:?})", fixed.root()),
            Head::Open(open) => format!("Open({open:?})"),
            Head::Residual => "Residual".to_owned(),
        };
        for (term, expected) in terms.iter().zip(expected) {
            for reading in [PatternReading::AsWritten, PatternReading::UpToEquations] {
                assert_eq!(describe(classify_pattern(reading, term)), expected);
            }
            assert_eq!(describe(classify_value(term, &mut NoEvidence)), expected);
        }
        assert_eq!(
            Term::injection(Sort::simple("SortSub"), sort(), var("X")).shape(),
            Shape::Injection
        );
    }

    /// Acceptance (f25d900c): a cycle through a function is no rigid cycle; one through a free
    /// constructor or an injection is.
    #[test]
    fn a_rigid_cycle_runs_through_free_constructors_and_injections_only() {
        let int = Sort::simple("SortInt");
        let x = Variable::new("X", int.clone());
        let minus = Arc::new(Symbol {
            attributes: {
                let mut attributes = crate::term::SymbolAttributes::constructor();
                attributes.symbol_type = SymbolType::Function(FunctionType::Total);
                attributes.hook = Some("INT.sub".into());
                attributes
            },
            ..Symbol::constructor("Lbl'Unds'-Int'Unds'", vec![int.clone(); 2], int.clone())
        });
        let inc_pos = Arc::new(Symbol {
            attributes: {
                let mut attributes = crate::term::SymbolAttributes::constructor();
                attributes.symbol_type = SymbolType::Function(FunctionType::Total);
                attributes
            },
            ..Symbol::constructor("LblincPos", vec![int.clone()], int.clone())
        });
        let successor = Arc::new(Symbol::constructor("Lbls", vec![int.clone()], int.clone()));
        let wrap = Arc::new(Symbol {
            attributes: crate::term::SymbolAttributes::constructor().with_anywhere(true),
            ..Symbol::constructor("Lblwrap", vec![int.clone()], int.clone())
        });
        let one = Term::domain_value(int.clone(), "1");
        let through_function = apply(
            &inc_pos,
            vec![apply(&minus, vec![Term::variable(x.clone()), one])],
        );
        assert_eq!(rigid_occurrence(&x, &through_function), None);

        let through_constructor = apply(&successor, vec![Term::variable(x.clone())]);
        let cycle = rigid_occurrence(&x, &through_constructor).expect("X = s(X) is a cycle");
        assert_eq!(cycle.variable(), &x);
        assert_eq!(cycle.term(), &through_constructor);

        let injected = Term::injection(int.clone(), sort(), through_constructor.clone());
        assert!(rigid_occurrence(&x, &injected).is_some());
        assert_eq!(rigid_occurrence(&x, &Term::variable(x.clone())), None);
        assert_eq!(
            rigid_occurrence(&x, &apply(&wrap, vec![Term::variable(x.clone())])),
            None,
            "an equation head may rewrite its argument away"
        );
        assert_eq!(
            rigid_occurrence(
                &x,
                &apply(
                    &successor,
                    vec![apply(&wrap, vec![Term::variable(x.clone())])]
                )
            ),
            None
        );
        let y = Variable::new("Y", int);
        assert_eq!(rigid_occurrence(&y, &through_constructor), None);
    }

    /// Acceptance (Q6): one `assoc` or `idem` constructor decides nothing about its arguments;
    /// a free one pairs them.
    #[test]
    fn an_algebraic_constructor_is_not_the_same_application() {
        let assoc = symbol("f", 2, |symbol| symbol.attributes.associative = true);
        let idem = symbol("g", 2, |symbol| symbol.attributes.idempotent = true);
        let free = symbol("h", 2, |_| {});
        let a = apply(&symbol("a", 0, |_| {}), Vec::new());
        let b = apply(&symbol("b", 0, |_| {}), Vec::new());
        let c = apply(&symbol("c", 0, |_| {}), Vec::new());
        for algebraic in [&assoc, &idem] {
            let left = apply(algebraic, vec![a.clone(), var("X")]);
            let right = apply(
                algebraic,
                vec![apply(algebraic, vec![a.clone(), b.clone()]), c.clone()],
            );
            assert!(matches!(
                compare_roots(value(&left), value(&right)),
                RootComparison::SameAlgebraicSymbol
            ));
        }
        let left = apply(&free, vec![a.clone(), var("X")]);
        let right = apply(&free, vec![b.clone(), c.clone()]);
        let RootComparison::SameApplication(same) = compare_roots(value(&left), value(&right))
        else {
            panic!("a free constructor pairs its arguments");
        };
        let pairs = same.pairs().collect::<Vec<_>>();
        assert_eq!(pairs, [(&a, &b), (&var("X"), &c)]);
    }

    /// The remaining rows of `compare_roots`, and the witnesses built from them.
    #[test]
    fn distinct_roots_mint_clashes_and_distinctness() {
        let definition = definition();
        let constructor = symbol("c", 1, |_| {});
        let other = symbol("d", 1, |_| {});
        let one = Term::domain_value(sort(), "1");
        let two = Term::domain_value(sort(), "2");
        let injection = Term::injection(Sort::simple("SortSub"), sort(), var("X"));
        let application = apply(&constructor, vec![one.clone()]);
        let nullary = apply(&constructor, Vec::new());
        let another = apply(&other, vec![one.clone()]);
        let normal_head = internal(&definition, "wrap{}(z{}())");

        let RootComparison::Distinct(witness) = compare_roots(value(&application), value(&another))
        else {
            panic!("two free constructors with different names differ");
        };
        let clash = HeadClash::new(witness, application.clone(), another.clone());
        assert_eq!(clash.left(), &application);
        assert_eq!(clash.right(), &another);
        let _: Distinct = Distinct::of_roots(witness);
        assert_eq!(
            clash.clone().into_terms(),
            (application.clone(), another.clone())
        );
        for (left, right) in [
            (&application, &one),
            (&one, &application),
            (&application, &injection),
            (&injection, &one),
        ] {
            assert!(matches!(
                compare_roots(value(left), value(right)),
                RootComparison::Distinct(_)
            ));
        }
        assert!(matches!(
            compare_roots(value(&application), value(&nullary)),
            RootComparison::ArityMismatch
        ));
        assert!(matches!(
            compare_roots(value(&injection), value(&injection)),
            RootComparison::Injections
        ));
        let RootComparison::Distinct(_) = compare_roots(
            value(&internal(&definition, "s{}(z{}())")),
            fixed(classify_value(&normal_head, &mut Scanned(&definition))),
        ) else {
            panic!("a free constructor and an instance-normal equation head differ");
        };

        assert!(matches!(
            compare_roots(value(&one), value(&two)),
            RootComparison::DomainValues
        ));
        assert!(Distinct::of_domain_values(value(&one), value(&two)).is_some());
        assert!(Distinct::of_domain_values(value(&one), value(&one)).is_none());
        assert!(Distinct::of_domain_values(value(&one), value(&application)).is_none());
        assert!(Distinct::of_injection_sorts(&InjectionComparison::Distinct).is_some());
        assert!(Distinct::of_injection_sorts(&InjectionComparison::Undecided).is_none());
        assert!(
            Distinct::of_injection_sorts(&InjectionComparison::Compare(one.clone(), two.clone()))
                .is_none()
        );
        let left = apply(&constructor, vec![one.clone()]);
        let right = apply(&constructor, vec![two.clone()]);
        let RootComparison::SameApplication(same) = compare_roots(value(&left), value(&right))
        else {
            panic!("one free constructor pairs its arguments");
        };
        let argument = Distinct::of_domain_values(value(&one), value(&two))
            .expect("different domain values are distinct");
        let _: Distinct = Distinct::through_argument(same, argument);

        let residual = apply(
            &symbol("m", 1, |symbol| symbol.attributes.macro_or_alias = true),
            vec![one.clone()],
        );
        let residual_clash = HeadClash::residual_root(application.clone(), residual.clone());
        assert_eq!(residual_clash.right(), &residual);
        let overload_clash = HeadClash::overload_family(one.clone(), another.clone());
        assert_eq!(overload_clash.into_terms(), (one, another));
    }

    /// Two collections of one kind are compared as collections; of different kinds they differ.
    #[test]
    fn collection_roots_compare_by_kind() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                hooked-sort SortList{}
                    [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortNat{}, SortNat{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
                hooked-symbol listItem{}(SortNat{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.element")]
                hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let map = internal(&definition, "mapItem{}(z{}(), z{}())");
        let list = internal(&definition, "listItem{}(z{}())");
        assert_eq!(map.shape(), Shape::Collection(CollectionKind::Map));
        assert_eq!(list.shape(), Shape::Collection(CollectionKind::List));
        assert!(matches!(
            compare_roots(value(&map), value(&map)),
            RootComparison::Collections(CollectionKind::Map)
        ));
        assert!(matches!(
            compare_roots(value(&map), value(&list)),
            RootComparison::Distinct(_)
        ));
        assert!(matches!(
            compare_roots(value(&list), value(&Term::domain_value(sort(), "1"))),
            RootComparison::Distinct(_)
        ));
    }

    /// The mark is evidence only with groundness; construction marks free constructors.
    #[test]
    fn a_certified_ground_normal_form_is_ground_and_marked() {
        let definition = definition();
        let plain = internal(&definition, "wrap{}(z{}())");
        assert!(!certified_ground_normal_form(&plain));
        assert!(certified_ground_normal_form(&plain.with_evaluated_cache()));
        assert!(certified_ground_normal_form(&internal(
            &definition,
            "s{}(z{}())"
        )));
        assert!(!certified_ground_normal_form(&internal(
            &definition,
            "s{}(X:SortNat{})"
        )));
    }
}
