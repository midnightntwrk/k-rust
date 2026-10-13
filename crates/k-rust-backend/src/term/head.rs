//! Whether the root of a term is the root of every value the term denotes.
//!
//! A backend term denotes a value of the definition's model. A domain value, a sort injection,
//! an internal collection and an application of a free constructor are values whose root is
//! fixed by the term. An application of an equation head (an `anywhere` production that is not a
//! declared function) denotes the value of its normal form under the definition's equations, and
//! distinct normal forms are distinct values, so its root is the root of its value only when the
//! application is a normal form on every instance. A function application denotes whatever its
//! equations and hook make it, a variable ranges over values, and a macro or alias application
//! denotes a value preprocessing should have replaced. An uninterpreted application has no
//! individuating declaration or has identifying algebraic axioms; it stays open under every
//! reading and every normal-form oracle.
//!
//! An algorithm may refute two terms because their roots differ, replace an equation between two
//! terms by equations between their arguments, fail an occurs check, or prune a rule by a
//! subject's root only when each root involved is fixed. The symbol's role excludes algebraic
//! applications from fixed roots, so comparing two fixed applications of one symbol needs no
//! additional algebraic flag test. Only syntactic identity decides uninterpreted applications.
//!
//! The classifier has two entry points. `classify_pattern` reads a left-hand side under a
//! `PatternReading` and never consults evidence. `classify_value` reads a subject or operand as
//! the value it denotes, and fixes an equation-head root only with a [`NormalEvidence`] from the
//! oracle its caller names (`NormalForms`). Equation matching also reads an equation's
//! left-hand side through `classify_value`, with the oracle `RecordedPatterns`: a ground term
//! denotes one value, so where the definition holds evidence that the ground term an
//! equation-head application of the pattern denotes is a normal form, reading the pattern up to
//! equations is reading it as that value. Evidence that an equation-head application is a normal
//! form on every instance comes only from:
//!
//! - an equation scan that found no equation of the definition whose left-hand side may match an
//!   instance, in a definition whose equation selection reaches every term equation (the
//!   instance-normal token of `BackendDefinition::instance_normal`), including the token the
//!   load recorded after its check for the ground term an application written in an executable
//!   left-hand side denotes (`ValueClaims::pattern_token`);
//! - the simplifier's certificate, the `evaluated` mark;
//! - being a subterm of an application for which one of those holds;
//! - being the application an equation is tried on, whose root the equation rewrites as written.
//!
//! Syntactic shape (groundness, head kinds, `Term::concrete_after_normalization`, the declared
//! `injective` attribute) is never evidence.
//!
//! The instance-normal scan's syntactic unification test reads an equation's left-hand side
//! through `classify_value` too, with the oracle [`ScannedPatterns`]: it fixes an equation-head
//! application written there at its own root where the load-time check admits that head, which
//! is how a step of the normal-form model matches the pattern. That is evidence about the
//! pattern, never about a value, and it has its own source.
//!
//! The decisive outcomes carry witnesses built here: [`HeadClash`] (two terms whose roots
//! differ), `Apart` (two terms with disjoint denotations), `Distinct` (two ground terms that
//! denote distinct values) and [`RigidCycle`] (a
//! variable occurring in a term through free constructors and injections only).

#[cfg(feature = "check-normal-forms")]
pub(crate) mod check;

use std::marker::PhantomData;

use super::{HeadRole, InjectionComparison, Term, TermKind, Variable};
use crate::{
    confluence::{GateSite, UntaintedIndex},
    definition::{BackendDefinition, SelectionComplete},
    instance_normal::{InstanceNormal, NormalArguments},
    rule::{Predicate, term_index},
    simplify::scan::{FunctionTheory, NoOfferedEquationMatched, SimplificationTheory},
};

/// How a left-hand side is read. A subject or operand has no reading: it is always read as the
/// value it denotes (`classify_value`).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PatternReading {
    /// A rewrite rule's left-hand side, matched as written: an equation-head root is fixed.
    AsWritten,
    /// An equation's left-hand side or an implication pattern: an equation-head subterm denotes
    /// the value of its normal form, which the pattern does not fix. (Equation matching reads one
    /// that denotes a ground term whose token the load recorded as that value instead:
    /// [`RecordedPatterns`]; the instance-normal scan reads one whose head the check admits by
    /// its root instead: [`ScannedPatterns`].)
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
    /// An equation-head application written in a left-hand side the instance-normal scan tries,
    /// whose head the load-time check admits ([`ScannedPatterns`]): a step of the normal-form
    /// model matches it against a normal form only through that root. Evidence about a pattern,
    /// never about a value.
    ScannedPattern,
    /// A settled equation-head application of the load-time critical-pair join
    /// (`confluence::join`): a normal form on every instance of the pair the join decides, because
    /// no left-hand side of an executable equation unifies with it, or because it is the value of
    /// a variable of one of the pair's left-hand sides. It is read only by the matcher the join
    /// runs (`matching::match_with_settled_evidence`), never by a claim: neither the
    /// instance-normal token nor the simplifier's certificate is built from evidence.
    Settled,
}

impl NormalEvidence {
    /// The root of the application an equation is tried on, or of its overload lift, which the
    /// equation rewrites as written. One call site: the matcher's oracle, for a subject among its
    /// given heads, a set with exactly two insertion points (the equation root and the overload
    /// lift).
    #[must_use]
    pub(crate) fn given() -> Self {
        Self(Source::Given)
    }

    /// The simplifier's certificate: `Some` exactly for an equation-head application whose
    /// `evaluated` mark (`Term::with_evaluated_cache`) certifies its value
    /// (`TermAttributes::value_claimed`), whose root is then fixed without the equation scan
    /// of `BackendDefinition::instance_normal`.
    ///
    /// Only `simplify::simplify_root` sets the `evaluated` bit on an application that is not a
    /// free constructor. It does so on a ground term whose arguments carry the bit, and only when
    /// both equation scans end `NotApplicable`. Every equation that equation selection offers the
    /// head or a bare variable, in the function and simplification theories, failed to match the
    /// term: its `Evaluate` match failed, or its collection match had no solution. The bit is set
    /// only in a definition where that selection reaches every term equation that could match an
    /// application (`BackendDefinition::equation_selection_complete`). A simplification with an
    /// `\and` left-hand side, which is filed apart, disables the mark for the whole definition. A
    /// `requires` does not count: undecided it blocks the scan, refuted it makes the scan context
    /// dependent, and both withhold the bit. An equation whose left-hand side matched but that
    /// the evaluator set aside (`concrete`, `symbolic`, a binding outside the left-hand side, a
    /// predicate right-hand side) also withholds it.
    ///
    /// A failed `Evaluate` match holds on every instance, which is the test `instance_normal`
    /// applies. The mark certifies the value only where the term's index is untainted by the
    /// load-time critical-pair check (`confluence`) and the term's arguments' values are
    /// certified too. A ground term is its own only instance, and the matcher reads no path
    /// condition, so the certificate is independent of the path the term is met on. It is a property of the
    /// term's structure, and it survives any later substitution that keeps the term by pointer.
    ///
    /// The arguments carry the bit as well. So every equation-head subterm was certified the same
    /// way, and free-constructor, injection and domain-value subterms are values. A marked
    /// function argument (a stuck overloaded function) is allowed: equation matching defers on a
    /// function subject, so an equation can fail on the parent only through another position,
    /// and then it fails for every value of the function. A collection argument carries the bit
    /// when its elements do. The collection axioms only identify representations of one value,
    /// and matching compares collections as values. Each of these arguments is compared by the
    /// matcher's own arm for its kind when the parent is decomposed.
    #[must_use]
    pub(crate) fn certified(term: &Term) -> Option<Self> {
        (term.shape() == Shape::Application(HeadRole::EquationHead)
            && term.attributes().value_claimed())
        .then_some(Self(Source::Certified))
    }

    /// A settled root of the critical-pair join; the witness is minted only by the join's
    /// settledness test (`confluence::join`).
    #[must_use]
    pub(crate) fn settled(_witness: crate::confluence::SettledRoot) -> Self {
        Self(Source::Settled)
    }

    /// An instance-normal token: the term, or a term it is a subterm of, is a normal form on
    /// every instance. The token is zero-sized and names no term, so the caller passes only the
    /// token `BackendDefinition::instance_normal` returned for the classified application or for
    /// a term it is a subterm of, or the one the load recorded for it
    /// (`ValueClaims::pattern_token`).
    #[must_use]
    pub(crate) fn instance_normal(_token: InstanceNormal) -> Self {
        Self(Source::InstanceNormal)
    }

    /// The root of an equation-head application written in a left-hand side the instance-normal
    /// scan tries, whose index the load-time check leaves untainted; the witness is minted only
    /// by the gate (`confluence::ValueClaims::admit_at`). One call site: [`ScannedPatterns`].
    #[must_use]
    pub(crate) fn scanned_pattern(_witness: UntaintedIndex) -> Self {
        Self(Source::ScannedPattern)
    }

    /// Whether this is evidence about the value the application denotes: every source but a
    /// left-hand side read as written or by its root in the instance-normal scan.
    #[must_use]
    pub(crate) fn of_a_value(self) -> bool {
        !matches!(self.0, Source::AsWritten | Source::ScannedPattern)
    }
}

/// The simplifier's certificate that an application is a normal form on every path, the only
/// argument that lets `Term::with_evaluated_cache` set the `evaluated` mark.
///
/// It is built from three statements, each minted where it is established:
///
/// - `SelectionComplete`: the definition's equation selection reaches every term equation that
///   could match an application (`BackendDefinition::equation_selection_complete`);
/// - `NoOfferedEquationMatched<FunctionTheory>` and
///   `NoOfferedEquationMatched<SimplificationTheory>`: every function equation and every
///   simplification equation that selection offers the application failed to match it
///   (`simplify::scan::scan_term_theory`, one scan per theory).
///
/// Together they say that every term equation of the definition failed to match the application.
/// A failed match reads no path condition, so the statement holds on every path. The certificate
/// is evidence about the application's value only where the load-time critical-pair check
/// leaves the application's index untainted (`confluence::ValueClaims::admit`): there the
/// definition's normal-form model is a model of it, so a normal form is an element distinct
/// from every other normal form. It carries that bit to `TermAttributes::value_claimed`. A
/// caller outside the crate can name the type but not build a value:
///
/// ```compile_fail
/// use k_rust_backend::term::head::NormalFormCertificate;
/// fn certify(certificate: NormalFormCertificate) -> NormalFormCertificate {
///     NormalFormCertificate(())
/// }
/// ```
///
/// ```
/// use k_rust_backend::term::head::NormalFormCertificate;
/// fn certify(certificate: NormalFormCertificate) -> NormalFormCertificate {
///     certificate
/// }
/// ```
#[derive(Debug)]
pub struct NormalFormCertificate {
    /// Whether the application's index is untainted, so that the certificate is evidence about
    /// its value (`term::TermAttributes::value_claimed`).
    values: bool,
}

impl NormalFormCertificate {
    #[must_use]
    pub(crate) fn new(
        _selection: SelectionComplete,
        _function_scan: NoOfferedEquationMatched<FunctionTheory>,
        _simplification_scan: NoOfferedEquationMatched<SimplificationTheory>,
        untainted: Option<UntaintedIndex>,
    ) -> Self {
        Self {
            values: untainted.is_some(),
        }
    }

    /// Whether the certificate is evidence about the application's value as well.
    pub(crate) fn certifies_values(&self) -> bool {
        self.values
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
pub(crate) struct NoEvidence;

impl NormalForms for NoEvidence {
    fn evidence(&mut self, _application: &Term) -> Option<NormalEvidence> {
        None
    }
}

/// The simplifier's certificate only (structural distinctness).
pub(crate) struct CertifiedOnly;

impl NormalForms for CertifiedOnly {
    fn evidence(&mut self, application: &Term) -> Option<NormalEvidence> {
        NormalEvidence::certified(application)
    }
}

/// The instance-normal scan of the definition only (unification).
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

/// The left-hand side of an equation in equation matching: an equation-head application written
/// there that denotes one ground term (ground once each `\and` in it keeps its structured
/// conjunct) is that normal form when the load recorded the term's instance-normal token after
/// the check (`ValueClaims::pattern_token`, filled by `BackendDefinition::record_pattern_tokens`).
/// That is the scan's answer for an equal subject, so a ground normal form is read alike on both
/// sides of a match. Gives nothing while the check runs (the withheld verdict holds no token),
/// and nothing for an application the record does not hold as written: one with a variable no
/// conjunction names, or a copy of the equation renamed apart from a subject that shares its
/// variable names (`rule::rename_apart`), which is then read up to equations.
pub(crate) struct RecordedPatterns<'d>(pub &'d BackendDefinition);

impl NormalForms for RecordedPatterns<'_> {
    fn evidence(&mut self, application: &Term) -> Option<NormalEvidence> {
        self.0
            .value_claims()
            .pattern_token(application)
            .map(NormalEvidence::instance_normal)
    }
}

/// The equation side of the instance-normal scan's syntactic unification test: an equation-head
/// application written in the scanned equation's left-hand side is fixed at its own root when
/// its symbol is not overloaded and the load-time check admits its index at the scan's gate site
/// (`GateSite::EquationHead`), and is read up to equations otherwise.
///
/// The scan asks whether an equation the definition's normal-form model `M_NF` offers at the
/// subject can match a normal-form instance of it. A step of `M_NF` matches the left-hand side
/// modulo injection composition, the overload axioms and the collection axioms, not modulo the
/// equations, so it matches an equation-head pattern `g(…)` against a normal form only through
/// the root `g`. The equation's membership axiom also holds of values that only reduce to an
/// instance of `g(…)`; whether `M_NF` satisfies the equation at those values is what the check's
/// pairs at that argument position answer, and a pair there that does not join taints both
/// equations and every symbol they mention. So where `g` is admitted, every equation that
/// mentions it joined at its `g` positions and the root reading decides the `M_NF` question.
/// The gate is asked at `g` itself, not only through the scanned head: the scan also reads
/// `symbolic` equations and simplification lemmas, which the check's closure does not cover, so
/// a lemma or `symbolic` equation rooted at another head `h` that nests a withdrawn `g` keeps
/// `g` open even though `h` keeps its claims. A lemma or `symbolic` equation rooted at `g`
/// itself is paired by no check, so it does not withdraw `g`; that the values it adds to `g(…)`
/// beyond its root are values `M_NF` gives `g(…)` rests only on the contract's assumption that
/// such an equation is a theorem of the executable ones.
/// An overloaded production is never fixed here: the overload axioms equate `g(inj(x))` with
/// `inj(l(x))`, which a match modulo those axioms reaches through another root. While the check
/// runs the gate admits nothing, so the check's own verdicts do not depend on this reading.
pub(crate) struct ScannedPatterns<'d>(pub &'d BackendDefinition);

impl NormalForms for ScannedPatterns<'_> {
    fn evidence(&mut self, application: &Term) -> Option<NormalEvidence> {
        let TermKind::Application { symbol, .. } = application.kind() else {
            return None;
        };
        if self.0.overloads().is_overloaded(&symbol.name)
            && !crate::confluence::switches::active().root_read_overloaded_patterns
        {
            return None;
        }
        self.0
            .value_claims()
            .admit_at(self.0, &term_index(application), GateSite::EquationHead)
            .map(NormalEvidence::scanned_pattern)
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
        refutable_arguments: bool,
    },
    /// An equation head read up to equations, or read as a value without evidence.
    EquationHead,
    /// No declaration or normal-form evidence individuates the application.
    Uninterpreted,
}

/// The classification of a root.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Head<'t> {
    Fixed(Fixed<'t>),
    Open(Open),
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

/// Classify a subject or operand as the value it denotes, or an equation's left-hand side read
/// as the values it denotes with the oracle [`RecordedPatterns`], or read by the roots the
/// instance-normal scan fixes with the oracle [`ScannedPatterns`]. Asks `normal` for evidence only
/// for an equation-head root, and only once. Evidence of a left-hand side's reading
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
            HeadRole::Function {
                injective,
                refutable_arguments,
                ..
            } => Head::Open(Open::Function {
                injective,
                refutable_arguments,
            }),
            HeadRole::Residual => Head::Residual,
            HeadRole::Uninterpreted => Head::Open(Open::Uninterpreted),
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
    Distinct(RootsDiffer<'t>),
    /// One free symbol, equal sort arguments, equal arity: the two values are equal exactly
    /// when the arguments are.
    SameApplication(SameApplication<'t>),
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
            expect(
                dead_code,
                reason = "the matcher and the unifier decide two collections in arms of their own"
            )
        )]
        CollectionKind,
    ),
}

/// Compare two fixed roots. Each side is matched on its own, so every pair of root kinds is
/// named.
#[must_use]
#[deny(clippy::wildcard_enum_match_arm)]
pub(crate) fn compare_roots<'t>(left: Fixed<'t>, right: Fixed<'t>) -> RootComparison<'t> {
    let differ = RootComparison::Distinct(RootsDiffer::new(left.term, right.term));
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
    } else {
        RootComparison::SameApplication(SameApplication {
            left: left_arguments,
            right: right_arguments,
        })
    })
}

/// Witness that the roots of two classified terms differ. It borrows the two compared terms in
/// every build; debug builds keep the borrowed handles, for [`RootsDiffer::release`] to record
/// which allocations were compared, and release builds, which check nothing, make it zero-sized.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RootsDiffer<'t> {
    #[cfg(debug_assertions)]
    left: &'t Term,
    #[cfg(debug_assertions)]
    right: &'t Term,
    borrow: PhantomData<&'t Term>,
}

impl<'t> RootsDiffer<'t> {
    /// The witness for two terms whose roots [`compare_roots`] found distinct.
    fn new(left: &'t Term, right: &'t Term) -> Self {
        #[cfg(not(debug_assertions))]
        let _ = (left, right);
        Self {
            #[cfg(debug_assertions)]
            left,
            #[cfg(debug_assertions)]
            right,
            borrow: PhantomData,
        }
    }

    /// The witness without its borrow of the two compared terms, so that their owner can move
    /// its handles of them into [`HeadClash::new`]: a borrowing witness would keep the owner
    /// from moving the handles it borrows, and cloning them instead would cost two reference
    /// count updates per refutation, the common outcome of a rule attempt. Debug builds keep
    /// which allocations were compared, and `HeadClash::new` checks that it is given those.
    #[must_use]
    pub(crate) fn release(self) -> ReleasedRoots {
        ReleasedRoots {
            #[cfg(debug_assertions)]
            compared: (allocation(self.left), allocation(self.right)),
        }
    }
}

/// A [`RootsDiffer`] whose borrow has ended ([`RootsDiffer::release`]): the roots of two terms,
/// which the holder owns, differ. Built only from a `RootsDiffer`; zero-sized in release
/// builds.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ReleasedRoots {
    /// The allocations of the two compared terms, left first.
    #[cfg(debug_assertions)]
    compared: (usize, usize),
}

/// The address of a term's allocation, which every handle of the term shares.
#[cfg(debug_assertions)]
fn allocation(term: &Term) -> usize {
    std::sync::Arc::as_ptr(&term.0).addr()
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
    /// caller already holds for the two classified terms, which the released witness no longer
    /// borrows.
    #[must_use]
    pub(crate) fn new(witness: ReleasedRoots, left: Term, right: Term) -> Self {
        #[cfg(debug_assertions)]
        assert_eq!(
            witness.compared,
            (allocation(&left), allocation(&right)),
            "a head clash holds the terms its witness compared"
        );
        #[cfg(not(debug_assertions))]
        let _ = witness;
        Self { left, right }
    }

    /// A clash between an application of an overloaded production and another root, in either
    /// order, where the overloaded side is not fixed under its reading. It holds only because an
    /// overloaded production has no equations besides its overload equations, which the backend
    /// does not check (open question Q2 of the classifier's design).
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

/// Witness that no value of one term is a value of the other, on every valuation: their denotations are disjoint.
/// Zero-sized; minted only here, from the facts that separate two roots.
/// It says nothing about definedness: two apart terms are \equals exactly where both are \bottom ([`Apart::equality`]).
#[derive(Debug)]
#[must_use]
pub(crate) struct Apart(());

impl Apart {
    /// Two fixed roots that differ have disjoint denotations.
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

    /// Two applications of one free symbol are apart when a pair of their arguments is.
    pub(crate) fn through_argument(_same: SameApplication<'_>, _argument: Apart) -> Self {
        Self(())
    }

    /// R-eq: disjoint denotations are equal exactly when both are empty.
    /// A provably defined side rules out equality; otherwise both sides must be undefined.
    pub(crate) fn equality(
        self,
        left: Term,
        right: Term,
        defined: impl Fn(&Term) -> bool,
    ) -> Predicate {
        if defined(&left) || defined(&right) {
            Predicate::False
        } else {
            Predicate::And(vec![
                Predicate::Not(Box::new(Predicate::Ceil(left))),
                Predicate::Not(Box::new(Predicate::Ceil(right))),
            ])
        }
    }
}

/// Witness that two concrete terms denote distinct values, the answer of `Term::structurally_distinct_with`.
/// Zero-sized; minted only from an [`Apart`] after the caller's concrete-term gate.
#[derive(Debug)]
pub(crate) struct Distinct(());

impl Distinct {
    /// R-ground: concrete terms contain no variables or function applications.
    /// The apartness witness uses a certificate for any equation head that decides, so the concrete pair denotes different values.
    #[must_use]
    pub(crate) fn of_concrete(_apart: Apart) -> Self {
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
pub(crate) fn rigid_occurrence(variable: &Variable, term: &Term) -> Option<RigidCycle> {
    let below = match term.shape() {
        Shape::Injection | Shape::Application(HeadRole::FreeConstructor) => {
            occurs_rigidly(variable, term)
        }
        Shape::Application(
            HeadRole::EquationHead
            | HeadRole::Function { .. }
            | HeadRole::Uninterpreted
            | HeadRole::Residual,
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
            HeadRole::EquationHead
            | HeadRole::Function { .. }
            | HeadRole::Uninterpreted
            | HeadRole::Residual => false,
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
pub(crate) fn certified_ground_normal_form(term: &Term) -> bool {
    term.concrete_after_normalization() && term.attributes().value_claimed()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    use crate::term::{AlgebraicAxioms, FunctionType, Sort, Symbol, SymbolType};

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
        let marked = plain.with_evaluated_mark_for_test();
        let redex = internal(&definition, "wrap{}(s{}(z{}()))").with_evaluated_mark_for_test();
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
        // The scan's equation side fixes an admitted head's root as the pattern writes it, also
        // on an application an equation reaches, and that evidence is not about a value.
        let pattern = Some(FixedRoot::EquationHead(NormalEvidence(
            Source::ScannedPattern,
        )));
        assert_eq!(root(&redex, &mut ScannedPatterns(&definition)), pattern);
        assert_eq!(root(&plain, &mut ScannedPatterns(&definition)), pattern);
        assert!(!NormalEvidence(Source::ScannedPattern).of_a_value());
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
            "Open(Uninterpreted)",
            "Open(Function { injective: true, refutable_arguments: true })",
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

    /// An algebraic application stays open; a free application pairs its arguments.
    #[test]
    fn an_algebraic_application_has_no_fixed_root() {
        let assoc = symbol("f", 2, |symbol| {
            symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
            symbol.attributes = symbol
                .attributes
                .clone()
                .with_algebraic_axioms(AlgebraicAxioms::assoc());
        });
        let idem = symbol("g", 2, |symbol| {
            symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
            symbol.attributes = symbol
                .attributes
                .clone()
                .with_algebraic_axioms(AlgebraicAxioms::idem());
        });
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
                classify_value(&left, &mut NoEvidence),
                Head::Open(Open::Uninterpreted)
            ));
            assert!(matches!(
                classify_value(&right, &mut NoEvidence),
                Head::Open(Open::Uninterpreted)
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
    fn distinct_roots_mint_clashes_and_apartness() {
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
        let clash = HeadClash::new(witness.release(), application.clone(), another.clone());
        assert_eq!(clash.left(), &application);
        assert_eq!(clash.right(), &another);
        let _: Apart = Apart::of_roots(witness);
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
        assert!(Apart::of_domain_values(value(&one), value(&two)).is_some());
        assert!(Apart::of_domain_values(value(&one), value(&one)).is_none());
        assert!(Apart::of_domain_values(value(&one), value(&application)).is_none());
        assert!(Apart::of_injection_sorts(&InjectionComparison::Distinct).is_some());
        assert!(Apart::of_injection_sorts(&InjectionComparison::Undecided).is_none());
        assert!(
            Apart::of_injection_sorts(&InjectionComparison::Compare(one.clone(), two.clone()))
                .is_none()
        );
        let left = apply(&constructor, vec![one.clone()]);
        let right = apply(&constructor, vec![two.clone()]);
        let RootComparison::SameApplication(same) = compare_roots(value(&left), value(&right))
        else {
            panic!("one free constructor pairs its arguments");
        };
        let argument = Apart::of_domain_values(value(&one), value(&two))
            .expect("different domain values are apart");
        let _: Apart = Apart::through_argument(same, argument);

        let residual = apply(
            &symbol("m", 1, |symbol| symbol.attributes.macro_or_alias = true),
            vec![one.clone()],
        );
        let residual_clash = HeadClash::residual_root(application.clone(), residual.clone());
        assert_eq!(residual_clash.right(), &residual);
        let overload_clash = HeadClash::overload_family(one.clone(), another.clone());
        assert_eq!(overload_clash.into_terms(), (one, another));
    }

    /// The ground reading consumes the disjoint-denotation witness of two concrete values.
    #[test]
    fn concrete_apartness_mints_distinctness() {
        let one = Term::domain_value(sort(), "1");
        let two = Term::domain_value(sort(), "2");
        assert!(one.concrete_after_normalization() && two.concrete_after_normalization());
        let apart = Apart::of_domain_values(value(&one), value(&two))
            .expect("different domain values are apart");
        let _: Distinct = Distinct::of_concrete(apart);
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
        assert!(certified_ground_normal_form(
            &plain.with_evaluated_mark_for_test()
        ));
        assert!(certified_ground_normal_form(&internal(
            &definition,
            "s{}(z{}())"
        )));
        assert!(!certified_ground_normal_form(&internal(
            &definition,
            "s{}(X:SortNat{})"
        )));
    }

    /// Acceptance (4045b87b): the ground `wrap(s(z))` without the certificate is open under the
    /// certificate-only oracle, so no fixed root and no argument pair yields a `Distinct`, and
    /// structural distinctness leaves `wrap(s(z)) = wrap(z)` undecided, which the equation
    /// `wrap(s(z)) = wrap(z)` makes true. The pre-fix shape returned `true` from `bool` for two
    /// ground applications on their names and arguments; the answer is now an
    /// `Option<Distinct>`, and the only mints need a fixed root.
    #[test]
    fn an_uncertified_ground_equation_head_is_not_structurally_distinct() {
        let definition = definition();
        let redex = internal(&definition, "wrap{}(s{}(z{}()))");
        let normal = internal(&definition, "wrap{}(z{}())");
        let undecided = |_: &Term, _: &Term| InjectionComparison::Undecided;
        assert!(redex.concrete_after_normalization() && !redex.attributes().evaluated);
        assert!(matches!(
            classify_value(&redex, &mut CertifiedOnly),
            Head::Open(Open::EquationHead)
        ));
        assert!(
            redex
                .structurally_distinct_with(&normal, &undecided)
                .is_none()
        );
        assert!(
            normal
                .structurally_distinct_with(&redex, &undecided)
                .is_none()
        );
        assert!(
            redex
                .structurally_distinct_with(&normal.with_evaluated_mark_for_test(), &undecided)
                .is_none(),
            "one side without the certificate decides nothing"
        );
        // Controls: two certified normal forms of `wrap`, and two free-constructor applications,
        // are distinct through a witness.
        let deeper = internal(&definition, "wrap{}(s{}(s{}(z{}())))");
        assert!(
            deeper
                .with_evaluated_mark_for_test()
                .structurally_distinct_with(&normal.with_evaluated_mark_for_test(), &undecided)
                .is_some()
        );
        let one = internal(&definition, "s{}(z{}())");
        let zero = internal(&definition, "z{}()");
        assert!(one.structurally_distinct_with(&zero, &undecided).is_some());
        assert!(!redex.structurally_distinct_after_normalization(&normal));
        assert!(one.structurally_distinct_after_normalization(&zero));
    }

    /// How a structural distinctness test compares two injections with different sorts.
    type InjectionOracle<'o> = dyn Fn(&Term, &Term) -> InjectionComparison + 'o;

    /// `Term::structurally_distinct_with` before it returned a witness, transcribed as a
    /// predicate over the declared role and the `evaluated` mark: the oracle of
    /// `structural_distinctness_decides_the_pairs_it_decided_as_a_predicate`.
    fn predicate_structurally_distinct(
        left: &Term,
        right: &Term,
        injections: &dyn Fn(&Term, &Term) -> InjectionComparison,
    ) -> bool {
        let certified_normal_application = |term: &Term| match term.kind() {
            TermKind::Application { symbol, .. } => {
                symbol.attributes.head_role() == HeadRole::FreeConstructor
                    || term.attributes().value_claimed()
            }
            _ => false,
        };
        if left == right
            || !left.concrete_after_normalization()
            || !right.concrete_after_normalization()
        {
            return false;
        }
        match (left.kind(), right.kind()) {
            (
                TermKind::DomainValue {
                    sort: left_sort,
                    value: left_value,
                },
                TermKind::DomainValue {
                    sort: right_sort,
                    value: right_value,
                },
            ) => left_sort != right_sort || left_value != right_value,
            (
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
            ) => {
                if !certified_normal_application(left) || !certified_normal_application(right) {
                    return false;
                }
                if left_symbol.name != right_symbol.name || left_sorts != right_sorts {
                    return true;
                }
                left_arguments
                    .iter()
                    .zip(right_arguments)
                    .any(|(left, right)| predicate_structurally_distinct(left, right, injections))
            }
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    term: left_operand,
                },
                TermKind::Injection {
                    source: right_source,
                    target: right_target,
                    term: right_operand,
                },
            ) => {
                if left_source == right_source && left_target == right_target {
                    return predicate_structurally_distinct(
                        left_operand,
                        right_operand,
                        injections,
                    );
                }
                match injections(left, right) {
                    InjectionComparison::Distinct => true,
                    InjectionComparison::Compare(left, right) => {
                        predicate_structurally_distinct(&left, &right, injections)
                    }
                    InjectionComparison::Undecided => false,
                }
            }
            (TermKind::Application { .. }, TermKind::Injection { .. }) => {
                certified_normal_application(left)
            }
            (TermKind::Injection { .. }, TermKind::Application { .. }) => {
                certified_normal_application(right)
            }
            _ => false,
        }
    }

    /// Structural distinctness answers with a witness exactly where the predicate it replaced
    /// answered `true`, on every ordered pair of a set of ground terms covering each root kind
    /// (domain values, free constructors, certified and uncertified equation heads, injections
    /// with equal and different sorts, a collection, a function application, a macro), those
    /// terms under one free constructor, and three injection oracles. The terms leave out the
    /// three pairs the witness deliberately does not decide (asserted in
    /// `structural_distinctness_leaves_algebraic_ill_formed_and_residual_pairs_undecided`).
    #[test]
    fn structural_distinctness_decides_the_pairs_it_decided_as_a_predicate() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                sort SortNat{} []
                hooked-sort SortList{}
                    [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
                symbol z{}() : SortNat{} [constructor{}(), functional{}(), injective{}()]
                hooked-symbol listUnit{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
                hooked-symbol listItem{}(SortNat{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.element")]
                hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        let lists =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let list = internal(&lists, "listItem{}(z{}())");
        assert_eq!(list.shape(), Shape::Collection(CollectionKind::List));

        let c = symbol("c", 1, |_| {});
        let d = symbol("d", 1, |_| {});
        let n = symbol("n", 0, |_| {});
        let wrap = symbol("wrap", 1, |symbol| {
            symbol.attributes = symbol.attributes.clone().with_anywhere(true);
        });
        let residual = symbol("m", 1, |symbol| symbol.attributes.macro_or_alias = true);
        let one = Term::domain_value(sort(), "1");
        let two = Term::domain_value(sort(), "2");
        let other_sort = Term::domain_value(Sort::simple("SortT"), "1");
        let nullary = apply(&n, Vec::new());
        let sub = Sort::simple("SortSub");
        let base = vec![
            one.clone(),
            two.clone(),
            other_sort.clone(),
            nullary.clone(),
            apply(&c, vec![one.clone()]),
            apply(&c, vec![two.clone()]),
            apply(&d, vec![one.clone()]),
            apply(&wrap, vec![one.clone()]),
            apply(&wrap, vec![one.clone()]).with_evaluated_mark_for_test(),
            apply(&wrap, vec![two.clone()]).with_evaluated_mark_for_test(),
            Term::injection(sub.clone(), sort(), one.clone()),
            Term::injection(sub.clone(), sort(), two.clone()),
            Term::injection(Sort::simple("SortOther"), sort(), two.clone()),
            Term::injection(sub.clone(), sort(), apply(&wrap, vec![one.clone()])),
            list,
            apply(&function("f", 1), vec![one.clone()]),
            apply(&residual, vec![one.clone()]),
        ];
        let terms = base
            .iter()
            .cloned()
            .chain(base.iter().map(|term| apply(&c, vec![term.clone()])))
            .collect::<Vec<_>>();
        let operand = |term: &Term| match term.kind() {
            TermKind::Injection { term, .. } => term.clone(),
            _ => unreachable!("the oracle is called on two injections"),
        };
        let undecided = |_: &Term, _: &Term| InjectionComparison::Undecided;
        let distinct = |_: &Term, _: &Term| InjectionComparison::Distinct;
        let compare =
            |left: &Term, right: &Term| InjectionComparison::Compare(operand(left), operand(right));
        let oracles: [&InjectionOracle<'_>; 3] = [&undecided, &distinct, &compare];
        let mut decided = 0;
        for injections in oracles {
            for left in &terms {
                for right in &terms {
                    let expected = predicate_structurally_distinct(left, right, injections);
                    assert_eq!(
                        left.structurally_distinct_with(right, injections).is_some(),
                        expected,
                        "{left:?} against {right:?}"
                    );
                    decided += usize::from(expected);
                }
            }
        }
        assert!(decided > 0 && decided < 3 * terms.len() * terms.len());
    }

    /// Algebraic applications have no fixed root or concrete normalized shape. Applications
    /// with different arities are ill-formed, and a macro denotes an unknown expansion.
    /// No structural distinction is justified for these pairs.
    #[test]
    fn structural_distinctness_leaves_algebraic_ill_formed_and_residual_pairs_undecided() {
        let undecided = |_: &Term, _: &Term| InjectionComparison::Undecided;
        let a = apply(&symbol("a", 0, |_| {}), Vec::new());
        let b = apply(&symbol("b", 0, |_| {}), Vec::new());
        let c = apply(&symbol("c", 0, |_| {}), Vec::new());
        let assoc = symbol("f", 2, |symbol| {
            symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
            symbol.attributes = symbol
                .attributes
                .clone()
                .with_algebraic_axioms(AlgebraicAxioms::assoc());
        });
        let idem = symbol("g", 2, |symbol| {
            symbol.attributes.symbol_type = SymbolType::Function(FunctionType::Total);
            symbol.attributes = symbol
                .attributes
                .clone()
                .with_algebraic_axioms(AlgebraicAxioms::idem());
        });
        for algebraic in [&assoc, &idem] {
            let left = apply(
                algebraic,
                vec![apply(algebraic, vec![a.clone(), b.clone()]), c.clone()],
            );
            let right = apply(
                algebraic,
                vec![a.clone(), apply(algebraic, vec![b.clone(), c.clone()])],
            );
            assert!(!left.concrete_after_normalization());
            assert!(!right.concrete_after_normalization());
            assert!(!predicate_structurally_distinct(&left, &right, &undecided));
            assert!(
                left.structurally_distinct_with(&right, &undecided)
                    .is_none()
            );
        }
        let k = symbol("k", 1, |_| {});
        let unary = apply(&k, vec![a.clone()]);
        let binary = apply(&k, vec![b.clone(), c.clone()]);
        assert!(predicate_structurally_distinct(&unary, &binary, &undecided));
        assert!(
            unary
                .structurally_distinct_with(&binary, &undecided)
                .is_none()
        );
        let residual = apply(
            &symbol("m", 1, |symbol| symbol.attributes.macro_or_alias = true),
            vec![a.clone()],
        )
        .with_evaluated_mark_for_test();
        assert!(predicate_structurally_distinct(&residual, &b, &undecided));
        assert!(
            residual
                .structurally_distinct_with(&b, &undecided)
                .is_none()
        );
    }
}
