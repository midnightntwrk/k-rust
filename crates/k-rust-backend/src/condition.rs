//! Rule and equation conditions, and their instances under a match.
//!
//! A condition `φ` is the `requires` or `ensures` of a rule, an equation or a right-hand-side
//! alternative, or a pattern's constraints read as the condition of a match (a claim's left-hand
//! side, an implication consequent, a search target). Under a substitution `σ`, `φσ` is a
//! predicate over the subject's instances, and a term in it denotes `\bottom` on an instance
//! where it is undefined: a K Boolean atom `b` means `\equals(b, true)`, which is `\bottom`
//! wherever `b` is, so `φσ` equals `φσ` with the definedness of each such atom stated
//! (`definedness::condition_definedness`).
//!
//! A [`Condition`] has no `&[Predicate]` view, so it cannot be substituted as a predicate list.
//! Its only instance is an `InstantiatedCondition`, whose predicates leave only with that
//! definedness stated (`InstantiatedCondition::with_definedness`) or through the condition's
//! simplification (`InstantiatedCondition::simplify`), which states it before anything but an
//! exact ground evaluation answers. A predicate derived from an instantiated condition therefore
//! reaches a solver or a decision only in definedness-explicit form.
//!
//! `eliminate_bindings` is the other half: eliminating a binding `x = t` of an element variable
//! keeps `\ceil(t)`.
//!
//! The conditions a simplification conjoins to its term, `t = C ∧ t'`, carry their role in
//! [`ResultConditions`], recorded where they are produced: each conjunct of `C` is an
//! [`Obligation`], part of the condition for `t'` to exist, or an assumption, an applied
//! equation's open `ensures`, which the definition asserts wherever that equation's instance
//! exists.

use std::{cell::Cell, collections::BTreeSet};

use crate::{
    deferred::{DeferredOutcome, deferred_obligations, deferred_positions},
    definedness::{ceil_term, condition_definedness},
    definition::BackendDefinition,
    diagnostic,
    rewrite::{Truth, predicates_truth, substitute_predicates},
    rule::{Predicate, rename_predicates},
    simplify::{RuleCondition, SimplificationError, hook_argument_definedness},
    stop::Stoppable,
    substitution::{Substitution, compose},
    term::{Term, TermKind, Variable, VariableKind},
};

/// The `requires` or `ensures` of a rule, an equation or a right-hand-side alternative as
/// written, over the rule's own variables.
///
/// It has no `&[Predicate]` view: an instance exists only as an `InstantiatedCondition`, whose
/// predicates leave with the definedness of their terms stated, because a condition is a
/// predicate over the instance and holds only where its terms are defined. Substituting the
/// condition as a predicate list does not type-check:
///
/// ```compile_fail,E0308
/// use k_rust_backend::{
///     rule::{Predicate, RewriteRule},
///     substitution::Substitution,
/// };
///
/// fn requires_instance(rule: &RewriteRule, substitution: Substitution) -> Vec<Predicate> {
///     k_rust_backend::rewrite::substitute_predicates(&rule.requires, &substitution)
/// }
/// ```
///
/// Reading the condition as written is allowed:
///
/// ```
/// use k_rust_backend::{
///     rule::{Predicate, RewriteRule},
///     substitution::Substitution,
/// };
///
/// fn requires_instance(rule: &RewriteRule, substitution: Substitution) -> Vec<Predicate> {
///     rule.requires.iter().cloned().collect()
/// }
/// ```
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Condition(Vec<Predicate>);

impl Condition {
    pub fn new(predicates: Vec<Predicate>) -> Self {
        Self(predicates)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// The conjuncts as written, read-only: for display, variable collection, SMT lemmas and the
    /// definedness analysis of the rule itself.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = &Predicate> + '_ {
        self.0.iter()
    }

    /// `self`, then the members of `other` it lacks: the `ensures` of a rule together with one
    /// right-hand-side alternative's.
    pub(crate) fn merged(&self, other: &Condition) -> Condition {
        let mut merged = self.0.clone();
        for predicate in &other.0 {
            if !merged.contains(predicate) {
                merged.push(predicate.clone());
            }
        }
        Self(merged)
    }

    /// The condition under a variable-to-variable renaming (`rule::rename_apart`). A variable
    /// denotes an element, so the renaming changes no term's definedness.
    pub(crate) fn rename(&self, rename: impl Copy + Fn(&Variable) -> Variable) -> Condition {
        Self(rename_predicates(&self.0, rename))
    }

    /// The condition under `substitution`, as a predicate over the subject's instances.
    pub(crate) fn instantiate(&self, substitution: &Substitution) -> InstantiatedCondition {
        #[expect(
            clippy::disallowed_methods,
            reason = "the instantiation entry point: callers state definedness through InstantiatedCondition, EquationInstance or eliminate_bindings"
        )]
        InstantiatedCondition(substitute_predicates(&self.0, substitution))
    }
}

/// A pattern's constraints read as the condition of a match: a claim's left-hand side or
/// right-hand side, an implication consequent, the antecedent of a negated-consequent query, a
/// search target. Under `substitution` they are a predicate over the subject's instances, which
/// holds only where their terms are defined, exactly as a rule's `requires` does.
pub(crate) fn instantiate_constraints(
    constraints: &[Predicate],
    substitution: &Substitution,
) -> InstantiatedCondition {
    #[expect(
        clippy::disallowed_methods,
        reason = "the instantiation entry point: callers state definedness through InstantiatedCondition, EquationInstance or eliminate_bindings"
    )]
    InstantiatedCondition(substitute_predicates(constraints, substitution))
}

/// A condition under a substitution. Its predicates leave only with the definedness of their
/// terms stated: [`Self::with_definedness`] states it now, and [`Self::simplify`] states it
/// before anything but an exact ground evaluation answers.
#[must_use]
pub(crate) struct InstantiatedCondition(Vec<Predicate>);

impl InstantiatedCondition {
    /// The instance under a renaming of its freshened existentials to fresh variables. A
    /// variable denotes an element, so the renaming changes no term's definedness.
    pub(crate) fn rename(self, renaming: &Substitution) -> Self {
        debug_assert!(
            renaming
                .values()
                .all(|value| matches!(value.kind(), TermKind::Variable(_))),
            "an instantiated condition is renamed only to variables"
        );
        #[expect(
            clippy::disallowed_methods,
            reason = "the instantiation entry point: callers state definedness through InstantiatedCondition, EquationInstance or eliminate_bindings"
        )]
        Self(substitute_predicates(&self.0, renaming))
    }

    /// The instance as one conjunction, as written, for a diagnostic that names a refuted
    /// condition (a refuted `ensures`). It is reported, never simplified or decided.
    pub(crate) fn report(&self) -> Predicate {
        match self.0.as_slice() {
            [] => Predicate::True,
            [predicate] => predicate.clone(),
            predicates => Predicate::And(predicates.to_vec()),
        }
    }

    /// The instance with the definedness of its terms stated
    /// (`definedness::condition_definedness`), an equivalent predicate; an obligation in `known`
    /// is not restated.
    pub(crate) fn with_definedness(
        self,
        definition: &BackendDefinition,
        known: &[Predicate],
    ) -> Result<Vec<Predicate>, DeferredOutcome> {
        condition_definedness(definition, self.0, known)
    }

    /// Simplify the instance with the definedness of its Boolean terms explicit
    /// (`definedness::condition_definedness`).
    ///
    /// `simplify(conditions, known, first_attempt)` simplifies under `known`; `definedness_known`
    /// are the predicates the stated obligations are deduplicated against (a superset of `known`).
    ///
    /// A condition without free variables is first simplified as it is, under no known predicate.
    /// If that decides it syntactically (`true` or `false`), the decision is exact and is returned.
    /// The simplifier evaluates a variable-free condition innermost first, and every step it takes
    /// is an equivalence that keeps the definedness of what it consumes: a builtin hook returns its
    /// arguments' obligations with its value, an equation carries the definedness of the terms it
    /// binds and decides its own requires with their definedness stated, and a partial function
    /// with no applicable equation stays an application, whose obligation keeps the atom from being
    /// `true` or `false`. So a `true` means every partial subterm evaluated to a value and is
    /// defined, and a `false` refutes the condition with or without the obligations. With no known
    /// predicate the decision rests on evaluation alone, never on an assumption about a term the
    /// evaluation left unevaluated. The solver sees nothing in this attempt except equation
    /// conditions whose definedness is explicit. Every other outcome, a symbolic condition, and a
    /// failure of the first attempt take the general path: the obligations are stated and the
    /// condition is simplified under `known`. A stop of the first attempt ends the condition with
    /// the stop, on the outer layer: the attempt has no answer, and the general path would answer
    /// in
    /// its place. The diagnostics of a discarded attempt are dropped, since the general path redoes
    /// and reports its work.
    pub(crate) fn simplify(
        self,
        definition: &BackendDefinition,
        known: &[Predicate],
        definedness_known: &[Predicate],
        mut simplify: impl FnMut(
            Vec<Predicate>,
            &[Predicate],
            bool,
        ) -> Stoppable<Result<Vec<Predicate>, SimplificationError>>,
    ) -> Stoppable<Result<Vec<Predicate>, SimplificationError>> {
        let conditions = self.0;
        let mut ceil_free = true;
        let mut ground = true;
        for condition in &conditions {
            condition.visit_terms(&mut |term| {
                ceil_free &= term.attributes().ceil_free();
                ground &= term.attributes().variables.is_empty();
            });
        }
        if ceil_free {
            return simplify(conditions, known, false);
        }
        if ground && !GENERAL_CONDITION_PATH.with(Cell::get) {
            let decided = |result: &Stoppable<Result<Vec<Predicate>, SimplificationError>>| {
                matches!(
                    result,
                    Ok(Ok(simplified)) if predicates_truth(simplified) != Truth::Unknown
                )
            };
            match diagnostic::attempt(|| simplify(conditions.clone(), &[], true), decided) {
                Ok(Ok(simplified)) if predicates_truth(&simplified) != Truth::Unknown => {
                    return Ok(Ok(simplified));
                }
                // A stop is handled first: the attempt has no answer, and the general path below
                // would answer in its place.
                Err(stop) => return Err(stop),
                Ok(_) => {}
            }
            // The general path redoes the nested conditions the attempt met; they take the general
            // path too, so a chain of nested conditions costs at most twice the general path
            // instead of doubling at every level.
            struct Restore(bool);
            impl Drop for Restore {
                fn drop(&mut self) {
                    GENERAL_CONDITION_PATH.with(|flag| flag.set(self.0));
                }
            }
            let _restore = Restore(GENERAL_CONDITION_PATH.with(|flag| flag.replace(true)));
            return match condition_definedness(definition, conditions, definedness_known) {
                Ok(conditions) => simplify(conditions, known, false),
                Err(outcome) => Ok(Err(outcome.into())),
            };
        }
        match condition_definedness(definition, conditions, definedness_known) {
            Ok(conditions) => simplify(conditions, known, false),
            Err(outcome) => Ok(Err(outcome.into())),
        }
    }
}

thread_local! {
    /// Set while `InstantiatedCondition::simplify` redoes a condition on the general path.
    static GENERAL_CONDITION_PATH: Cell<bool> = const { Cell::new(false) };
}

/// `predicates` under `bindings`, followed by `ceil_term` of each value bound to an element
/// variable (I2), minus the predicates in `known` or already among the result.
///
/// For an element variable `x` and a functional term `t`, `∃x. (x = t ∧ ψ)` is `⌈t⌉ ∧ ψ[t/x]`:
/// an element variable denotes a defined element, so no `x` equals `t` where `t` is undefined.
/// Replacing `x` by `t` without `⌈t⌉` would assert `ψ[t/x]` also where `t` is undefined, where the
/// binding has no instance. A set variable denotes any set of elements, `\bottom` included, so its
/// binding states nothing.
pub(crate) fn eliminate_bindings(
    definition: &BackendDefinition,
    predicates: &[Predicate],
    bindings: &Substitution,
    known: &[Predicate],
) -> Result<Vec<Predicate>, DeferredOutcome> {
    #[expect(
        clippy::disallowed_methods,
        reason = "the instantiation entry point: callers state definedness through InstantiatedCondition, EquationInstance or eliminate_bindings"
    )]
    let mut result = substitute_predicates(predicates, bindings);
    for (variable, value) in bindings {
        if variable.kind != VariableKind::Element || value.attributes().ceil_free() {
            continue;
        }
        for predicate in ceil_term(definition, value)? {
            if !known.contains(&predicate) && !result.contains(&predicate) {
                result.push(predicate);
            }
        }
    }
    Ok(result)
}

/// A substitution and the conditions a match or a unification found with it, each condition
/// stated over the variables the substitution leaves free (N).
///
/// `(sigma, C)` denotes the bindings `x = sigma(x)` conjoined with `C`. Claim and rule application
/// use `sigma` up: they instantiate the right-hand side and the `requires` by it and keep `C`
/// without restating the bindings. That reads the pair correctly only when no condition mentions a
/// variable `sigma` binds; a condition `phi(x)` recorded before a later step bound `x` to `t` would
/// keep `x` free and mean `exists x. phi(x)` where the match needs `phi(t)`.
///
/// The fields are private: a value is built by [`MatchSolution::from_parts`], which applies the
/// substitution to the conditions, and is taken apart only by [`MatchSolution::into_parts`]. For an
/// element variable `x`, `x = t and phi(x)` is `x = t and phi(t)`, and the binding stays in the
/// substitution, so no definedness is stated here; a consumer that drops a binding states it (I2).
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) struct MatchSolution {
    substitution: Substitution,
    conditions: Vec<Predicate>,
}

impl MatchSolution {
    /// A match substitution with no conditions.
    pub(crate) fn new(substitution: Substitution) -> Self {
        Self {
            substitution,
            conditions: Vec::new(),
        }
    }

    /// `conditions` under `substitution`, in their order. Only a condition that mentions a variable
    /// `substitution` binds is rewritten; without one, nothing is allocated.
    pub(crate) fn from_parts(substitution: Substitution, conditions: Vec<Predicate>) -> Self {
        let conditions = Self::normalized(&substitution, conditions);
        Self {
            substitution,
            conditions,
        }
    }

    fn normalized(substitution: &Substitution, conditions: Vec<Predicate>) -> Vec<Predicate> {
        #[expect(
            clippy::disallowed_methods,
            reason = "match conditions under the substitution they leave with: for an element variable x, x = t and phi(x) is x = t and phi(t), and the binding stays in the substitution"
        )]
        if conditions
            .iter()
            .any(|condition| mentions_bound_variable(condition, substitution))
        {
            substitute_predicates(&conditions, substitution)
        } else {
            conditions
        }
    }

    /// The bindings of this match, read-only so an extension cannot leave conditions stale.
    pub(crate) fn substitution(&self) -> &Substitution {
        &self.substitution
    }

    /// The conditions stated under this match's current substitution.
    pub(crate) fn conditions(&self) -> &[Predicate] {
        &self.conditions
    }

    /// Conjoin each condition under the current substitution, retaining the first occurrence.
    pub(crate) fn conjoin(&mut self, conditions: impl IntoIterator<Item = Predicate>) {
        for condition in Self::normalized(&self.substitution, conditions.into_iter().collect()) {
            if !self.conditions.contains(&condition) {
                self.conditions.push(condition);
            }
        }
    }

    /// Extend the bindings and restate earlier conditions under the composed substitution.
    /// The bindings stay in the match, so this preserves its conjunction without dropping
    /// any binding's definedness.
    pub(crate) fn bind(&mut self, bindings: &Substitution) {
        if !bindings.is_empty() {
            self.substitution = compose(bindings, &self.substitution);
            self.conditions =
                Self::normalized(&self.substitution, std::mem::take(&mut self.conditions));
        }
    }

    /// Put the conjuncts in canonical order and remove repetitions.
    pub(crate) fn sort_conditions(&mut self) {
        self.conditions.sort();
        self.conditions.dedup();
    }

    /// The substitution and its conditions. In debug builds this checks N; a condition that still
    /// mentions a bound variable means the substitution was not idempotent.
    pub(crate) fn into_parts(self) -> (Substitution, Vec<Predicate>) {
        debug_assert!(
            !self.conditions.iter().any(|condition| condition
                .free_variables()
                .iter()
                .any(|variable| self.substitution.contains_key(variable))),
            "a match condition mentions a variable its substitution binds: {self:?}"
        );
        (self.substitution, self.conditions)
    }
}

/// Whether a term of `predicate` has a variable `substitution` binds. Bound occurrences count too;
/// they only make the substitution a no-op there.
fn mentions_bound_variable(predicate: &Predicate, substitution: &Substitution) -> bool {
    let mut found = false;
    predicate.visit_terms(&mut |term| {
        found |= term
            .attributes()
            .variables
            .iter()
            .any(|variable| substitution.contains_key(variable));
    });
    found
}

/// The instance of an equation's left-hand side under its match (I1, I2): the equation's
/// `requires` under the match, and what the equation's use needs once that is decided.
///
/// An equation `f(X) = r requires R` is an axiom over every element `X`. A term `t` bound to `X`
/// is a functional pattern (at most one element), so the instance at `t` is
/// `f(t) = \ceil(t) /\ r[t]` where `R[t]` holds: both sides are empty where `t` is, and the
/// axiom applies on the one element otherwise. An argument pattern that is not a variable binds
/// its argument by membership, `f(Y) = r requires R /\ Y ∈ p(X)`, and an undefined term is a
/// member of no pattern, so the instance at `f(t)` with `t` an instance of `p(X)` is likewise
/// `\ceil(t) /\ r` ([`ConsumedDefinedness`]). The `\ceil` factors are the binding obligations
/// ([`BindingDefinedness`]); the right-hand side is reachable only after they are decided
/// ([`MatchedEquation::decide`]), and then only together with those that stay open
/// ([`DefinedEquation::into_result`], [`DefinedEquation::into_carried`]).
pub(crate) struct EquationInstance {
    requires: InstantiatedCondition,
    matched: MatchedEquation,
}

impl EquationInstance {
    /// The instance of `requires` under `substitution`, and the definedness of every term
    /// `substitution` binds to an element variable and of what the left-hand side consumes of
    /// the subject (`consumed`), minus what the instantiated `requires` already states.
    ///
    /// An element variable ranges over elements, so binding it to a term `t` asserts `\ceil(t)`;
    /// a set variable binds an arbitrary pattern and imposes no obligation. `ceil_term` already
    /// discharges constructors, total symbols and element variables, so the obligations name
    /// only partial applications, set variables and collection distinctness.
    ///
    /// A term a variable binds inside an operand of a short-circuit application of the subject
    /// that is not evaluated states its definedness as deferred atoms (`ConsumedDefinedness`),
    /// and one whose definedness depends on an impure application is the outcome.
    pub(crate) fn new(
        definition: &BackendDefinition,
        requires: &Condition,
        substitution: Substitution,
        consumed: ConsumedDefinedness,
    ) -> Result<Self, DeferredOutcome> {
        let requires = requires.instantiate(&substitution);
        let mut definedness = Vec::new();
        let mut add = |predicate: Predicate| {
            if !requires.0.contains(&predicate) && !definedness.contains(&predicate) {
                definedness.push(predicate);
            }
        };
        for (variable, value) in &substitution {
            if variable.kind == VariableKind::Element {
                let stated = consumed
                    .deferred_variables
                    .binding_definedness(definition, variable, value)?;
                for predicate in stated {
                    add(predicate);
                }
            }
        }
        for predicate in consumed.obligations {
            add(predicate);
        }
        Ok(Self {
            requires,
            matched: MatchedEquation {
                substitution,
                bindings: BindingDefinedness(definedness),
            },
        })
    }

    /// The `requires` to decide, during which the binding obligations are taken as known
    /// (`matched.bindings().as_known()`): they are the `\ceil(t)` factor of the instance, carried
    /// rather than decided by the `requires`. And the instance, whose use needs them decided.
    pub(crate) fn into_requires(self) -> (InstantiatedCondition, MatchedEquation) {
        (self.requires, self.matched)
    }
}

/// The definedness of what an equation's left-hand side consumes of its subject below the
/// subject's root, beyond the terms its match binds to variables.
///
/// An equation binds each argument of its root by membership in its argument pattern
/// (`f(Y) = r requires Y ∈ p(X)`), and an undefined term is a member of no pattern, so an
/// instance at `f(t1, ..., tn)` exists only where every `ti` is defined: its obligations include
/// `ceil_term(ti)` for every argument, whether a variable or a pattern consumes it. A pattern
/// built from free constructors, injections and collection units and elements loses nothing,
/// since those are defined exactly where their parts are and the parts are bound below; any
/// other pattern position keeps an obligation of its own: a function application (`pf(X)`
/// against `pf(d)`, which no equation reduces), an equation head whose claims are withdrawn, and
/// the distinctness of a map or set the pattern splits (`(c |-> V) M` against
/// `{c |-> 1, Y |-> 2}` consumes `\not(c = Y)`, which neither `V` nor `M` carries).
///
/// A simplification lemma `f(p(X)) = r` states its equality without memberships, but an
/// application is undefined wherever one of its arguments is, so its instance where `p(X)` is
/// undefined would equate an undefined term with `r`, making `r` empty there; the lemma is
/// therefore read as saying nothing at such an instance, and carries the same obligations.
///
/// An argument a variable binds whole is not charged here: an element variable's binding
/// obligation is the same `ceil_term` ([`EquationInstance::new`] states it), and a set variable
/// ranges over every pattern, the undefined one included, so its argument carries none. The
/// root itself is what the equation is about (its own `\ceil` is the equation's result), so it
/// consumes nothing: a collection at the root contributes its parts, not its own distinctness.
#[must_use]
pub(crate) struct ConsumedDefinedness {
    obligations: Vec<Predicate>,
    /// The left-hand side's variables whose bound terms state their definedness as deferred
    /// atoms ([`EquationInstance::new`]).
    deferred_variables: DeferredVariables,
}

impl ConsumedDefinedness {
    /// `ceil_term` of each immediate subterm of `subject` that `pattern`, an equation's
    /// left-hand side matched against `subject`, does not bind whole to a variable. Each
    /// argument with a stored `ceil_free` attribute costs one read of it.
    ///
    /// An operand of a short-circuit `subject` that is not evaluated states its definedness
    /// by `crate::deferred::deferred_obligations` instead of `ceil_term`, whose decision would
    /// evaluate it: the `#if` equations at sort `K` (`#if C #then B1 #else _ #fi => B1 requires
    /// C`) and the discarding equations of `andThenBool` and `orElseBool` apply where the hook
    /// cannot, and bind or consume such an operand. One whose definedness depends on an impure
    /// application is the outcome.
    pub(crate) fn of_arguments(
        definition: &BackendDefinition,
        pattern: &Term,
        subject: &Term,
    ) -> Result<Self, DeferredOutcome> {
        let positions = deferred_positions(subject);
        let mut obligations = Vec::new();
        let mut consume = |position: Option<usize>, argument: &Term| {
            if argument.attributes().ceil_free() {
                return Ok(());
            }
            let stated = match position {
                Some(position) if positions.contains(&position) => {
                    deferred_obligations(definition, argument)?
                }
                _ => ceil_term(definition, argument)?,
            };
            for predicate in stated {
                if !obligations.contains(&predicate) {
                    obligations.push(predicate);
                }
            }
            Ok::<_, DeferredOutcome>(())
        };
        match (pattern.kind(), subject.kind()) {
            (
                TermKind::Application {
                    arguments: patterns,
                    ..
                },
                TermKind::Application { arguments, .. },
            ) if patterns.len() == arguments.len() => {
                for (position, (pattern, argument)) in patterns.iter().zip(arguments).enumerate() {
                    if !matches!(pattern.kind(), TermKind::Variable(_)) {
                        consume(Some(position), argument)?;
                    }
                }
            }
            // A variable left-hand side binds the whole subject.
            (TermKind::Variable(_), _) => {}
            // A `ceil_free` child consumes nothing; a collection's are passed over through its
            // trees' summaries.
            _ => {
                for child in
                    crate::term::children_lacking(subject.kind(), crate::term::Flag::CeilFree)
                {
                    consume(None, child)?;
                }
            }
        }
        Ok(Self {
            obligations,
            deferred_variables: DeferredVariables::of([(pattern, subject)]),
        })
    }

    /// Obligations a caller computed from the term operands it consumes (a predicate
    /// equation's), with the variables its match binds only inside an operand that is not
    /// evaluated.
    pub(crate) fn stated(
        obligations: Vec<Predicate>,
        deferred_variables: DeferredVariables,
    ) -> Self {
        Self {
            obligations,
            deferred_variables,
        }
    }
}

/// The variables of an equation's left-hand side that occur only where its match reads an
/// operand of a `KEQUAL.ite`, `BOOL.andThen` or `BOOL.orElse` application of the subject that
/// is not evaluated (`crate::deferred::deferred_positions`), at the root of a subject term or
/// below it: a lemma `#if B #then X #else Y #fi +Int Z => ..` reaches a conditional below its
/// root, and a predicate lemma `{#if B #then X #else Y #fi #Equals Z} => ..` reaches one in a
/// term operand of the predicate. The term such a variable binds states its definedness as
/// deferred atoms ([`Self::binding_definedness`]).
///
/// The reading is by position in the left-hand side, not by the term bound: a variable under
/// such an operand's position binds a part of the operand whatever term the match builds for it
/// (the rest of a collection it splits, a value it injects again), which is no subterm of the
/// subject to be recognised by. A variable that also occurs at an evaluated position, of the
/// same term or of another operand of the predicate, binds a term equal to one the subject holds
/// evaluated, so it is not deferred.
///
/// The walk follows the left-hand side, so it costs its size and not the subject's. Where the
/// two do not align argument by argument (a collection pattern, matched up to the order of its
/// items), every variable below is read as deferred when the subject's part there holds an
/// operand that is not evaluated: the deferred reading states no less than the evaluated one
/// decides, so taking it for a variable bound outside the operand loses precision only.
#[derive(Clone, Default)]
pub(crate) struct DeferredVariables(BTreeSet<Variable>);

impl DeferredVariables {
    /// The deferred variables of a left-hand side whose terms are matched against the subject's
    /// in `pairs` (a term of the left-hand side, the subject term it is matched against): one
    /// pair for a term equation, one per term operand for a predicate equation.
    pub(crate) fn of<'a>(pairs: impl IntoIterator<Item = (&'a Term, &'a Term)>) -> Self {
        let mut deferred = BTreeSet::new();
        let mut evaluated = BTreeSet::new();
        let mut pending = pairs.into_iter().collect::<Vec<_>>();
        while let Some((pattern, subject)) = pending.pop() {
            collect_deferred_variables(
                pattern,
                subject,
                &mut deferred,
                &mut evaluated,
                &mut pending,
            );
        }
        deferred.retain(|variable| !evaluated.contains(variable));
        Self(deferred)
    }

    /// The definedness of `value`, the term the match binds to the element variable `variable`:
    /// the deferred atoms of `value` when the variable is deferred, whose decision evaluates
    /// nothing (`crate::deferred::deferred_obligations`), and `ceil_term(value)` otherwise. A
    /// deferred value whose definedness depends on an impure application is the outcome.
    pub(crate) fn binding_definedness(
        &self,
        definition: &BackendDefinition,
        variable: &Variable,
        value: &Term,
    ) -> Result<Vec<Predicate>, DeferredOutcome> {
        if self.0.contains(variable) {
            deferred_obligations(definition, value)
        } else {
            ceil_term(definition, value)
        }
    }
}

/// One step of [`DeferredVariables::of`]: read `pattern` against `subject`, adding the pairs
/// still to read to `pending`.
fn collect_deferred_variables<'a>(
    pattern: &'a Term,
    subject: &'a Term,
    deferred: &mut BTreeSet<Variable>,
    evaluated: &mut BTreeSet<Variable>,
    pending: &mut Vec<(&'a Term, &'a Term)>,
) {
    // A `ceil_free` part of the subject has no operand whose definedness is open.
    if subject.attributes().ceil_free() {
        return;
    }
    match (pattern.kind(), subject.kind()) {
        (TermKind::Variable(variable), _) => {
            evaluated.insert(variable.clone());
        }
        (TermKind::DomainValue { .. }, _) => {}
        (TermKind::And(left, right), _) => pending.extend([(left, subject), (right, subject)]),
        (
            TermKind::Application {
                symbol: pattern_symbol,
                arguments: patterns,
                ..
            },
            TermKind::Application {
                symbol, arguments, ..
            },
        ) if pattern_symbol.name == symbol.name && patterns.len() == arguments.len() => {
            let positions = deferred_positions(subject);
            for (position, (pattern, argument)) in patterns.iter().zip(arguments).enumerate() {
                if positions.contains(&position) {
                    collect_variables(pattern, deferred);
                } else {
                    pending.push((pattern, argument));
                }
            }
        }
        (TermKind::Injection { term: pattern, .. }, TermKind::Injection { term, .. }) => {
            pending.push((pattern, term));
        }
        _ => {
            let target = if holds_deferred_operand(subject) {
                deferred
            } else {
                evaluated
            };
            collect_variables(pattern, target);
        }
    }
}

/// The variables of `pattern`, added to `variables`.
fn collect_variables(pattern: &Term, variables: &mut BTreeSet<Variable>) {
    let mut pending = vec![pattern];
    while let Some(pattern) = pending.pop() {
        match pattern.kind() {
            TermKind::Variable(variable) => {
                variables.insert(variable.clone());
            }
            kind => pending.extend(crate::term::immediate_children(kind)),
        }
    }
}

/// Whether `term` holds a short-circuit application with an operand that is not evaluated. The
/// `ceil_free` parts are passed over, a collection's through its trees' summaries.
fn holds_deferred_operand(term: &Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if term.attributes().ceil_free() {
            continue;
        }
        if !deferred_positions(term).is_empty() {
            return true;
        }
        pending.extend(crate::term::children_lacking(
            term.kind(),
            crate::term::Flag::CeilFree,
        ));
    }
    false
}

/// An equation instance whose `requires` is to be, or has been, decided; its binding
/// obligations are not decided yet, so nothing its right-hand side instantiates is reachable.
#[must_use]
pub(crate) struct MatchedEquation {
    substitution: Substitution,
    bindings: BindingDefinedness,
}

impl MatchedEquation {
    pub(crate) fn substitution(&self) -> &Substitution {
        &self.substitution
    }

    pub(crate) fn bindings(&self) -> &BindingDefinedness {
        &self.bindings
    }

    /// Decide the binding obligations under the path condition, the only way to the instance's
    /// right-hand side.
    ///
    /// `decide(obligations)` simplifies the obligations and decides them, returning the verdict
    /// with the obligations as simplified. With no obligation the instance is defined as it
    /// stands and `decide` is not called. A satisfied verdict discharges the obligations, a
    /// refuted one makes a bound term empty under the path condition
    /// ([`DecidedEquation::Refuted`]),
    /// and an undecided one leaves the simplified obligations open, carried by the result.
    pub(crate) fn decide(
        self,
        decide: impl FnOnce(
            Vec<Predicate>,
        )
            -> Stoppable<Result<(RuleCondition, Vec<Predicate>), SimplificationError>>,
    ) -> Stoppable<Result<DecidedEquation, SimplificationError>> {
        let Self {
            substitution,
            bindings: BindingDefinedness(obligations),
        } = self;
        let open = if obligations.is_empty() {
            Vec::new()
        } else {
            match decide(obligations)? {
                Err(failure) => return Ok(Err(failure)),
                Ok((RuleCondition::Satisfied, _)) => Vec::new(),
                Ok((RuleCondition::Refuted, _)) => {
                    return Ok(Ok(DecidedEquation::Refuted(substitution)));
                }
                Ok((RuleCondition::Indeterminate(_), simplified)) => simplified,
            }
        };
        Ok(Ok(DecidedEquation::Defined(DefinedEquation {
            substitution,
            carried: CarriedObligations(open.into_iter().map(Obligation).collect()),
        })))
    }
}

/// `\ceil(t)` for every term `t` an equation's match binds to an element variable (I2), minus
/// what the instantiated `requires` already states.
#[must_use]
pub(crate) struct BindingDefinedness(Vec<Predicate>);

impl BindingDefinedness {
    /// The obligations as stated: taken as known while the equation's `requires` is decided,
    /// and read by the predicate-equation strictness test (`obligated_variables`).
    pub(crate) fn as_known(&self) -> &[Predicate] {
        &self.0
    }
}

/// The binding obligations of an equation instance, decided.
#[must_use]
pub(crate) enum DecidedEquation {
    /// The obligations are discharged or open; the instance is usable.
    Defined(DefinedEquation),
    /// A bound term is empty under the path condition. The match serves the predicate-equation
    /// strictness test (`strict_variables`).
    Refuted(Substitution),
}

/// An equation instance whose binding obligations are decided and not refuted.
#[must_use]
pub(crate) struct DefinedEquation {
    substitution: Substitution,
    carried: CarriedObligations,
}

impl DefinedEquation {
    pub(crate) fn substitution(&self) -> &Substitution {
        &self.substitution
    }

    /// Whether no binding obligation stays open.
    pub(crate) fn is_discharged(&self) -> bool {
        self.carried.is_empty()
    }

    /// The equation's `ensures` under the instance, a condition over the instance (I1).
    pub(crate) fn instantiate_ensures(&self, ensures: &Condition) -> InstantiatedCondition {
        ensures.instantiate(&self.substitution)
    }

    /// The right-hand side `predicates` of a ceil or predicate equation under the instance,
    /// followed by the open binding obligations: the instance is `\ceil(t) /\ q[t]`. It is the
    /// only view of the instantiated right-hand side, so the open obligations cannot be left
    /// out of it.
    pub(crate) fn into_result(self, predicates: &[Predicate]) -> Vec<Predicate> {
        #[expect(
            clippy::disallowed_methods,
            reason = "the instantiation entry point: callers state definedness through InstantiatedCondition, EquationInstance or eliminate_bindings"
        )]
        let mut result = substitute_predicates(predicates, &self.substitution);
        result.extend(self.carried.into_predicates());
        result
    }

    /// The open binding obligations of a function or `\top` equation's instance, which its
    /// result carries.
    pub(crate) fn into_carried(self) -> CarriedObligations {
        self.carried
    }
}

/// A conjunct of a simplification result that is part of the condition for the result to exist
/// (I4): the definedness of a term an equation binds or of an argument of an evaluated hooked
/// application, or a refutation.
///
/// It is produced by [`ResultConditions::obligations`], which leaves out the assumptions, by
/// `RhsDefinedness`, from an instantiated right-hand side, and for a rewrite rule's own open
/// `ensures` by `Obligation::of_rule_ensures`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Obligation(Predicate);

impl Obligation {
    pub fn as_predicate(&self) -> &Predicate {
        &self.0
    }

    pub fn into_predicate(self) -> Predicate {
        self.0
    }

    /// A rewrite rule's own `ensures`, instantiated, simplified and left undecided by the
    /// rewrite step: the rule's result exists only where it holds, so the result carries it.
    pub(crate) fn of_rule_ensures(predicate: Predicate) -> Self {
        Self(predicate)
    }
}

/// The definedness of an instantiated rewrite right-hand side: `\ceil` of every partial
/// subterm (`definedness::ceil_term`), which the rule's result needs in order to exist.
///
/// It is built only from the term, so no other predicate takes this role; in particular a
/// conjunct of the right-hand side's own simplification result (`ResultConditions`), which may
/// be an assumption, cannot be passed off as the right-hand side's definedness.
#[must_use]
pub(crate) struct RhsDefinedness(Vec<Predicate>);

impl RhsDefinedness {
    /// `ceil_term(definition, rhs)`.
    pub(crate) fn of(definition: &BackendDefinition, rhs: &Term) -> Result<Self, DeferredOutcome> {
        Ok(Self(ceil_term(definition, rhs)?))
    }

    /// The obligations, as stated or as simplified, for their decision and for the report of a
    /// refuted one.
    pub(crate) fn as_slice(&self) -> &[Predicate] {
        &self.0
    }

    /// The obligations replaced by their simplification under the condition knowledge, an
    /// equivalent condition on the instances that knowledge describes.
    pub(crate) fn simplify(
        self,
        simplify: impl FnOnce(&[Predicate]) -> Stoppable<Result<Vec<Predicate>, SimplificationError>>,
    ) -> Stoppable<Result<Self, SimplificationError>> {
        Ok(simplify(&self.0)?.map(Self))
    }

    /// The obligations an undecided definedness leaves for the result to carry.
    pub(crate) fn into_obligations(self) -> impl Iterator<Item = Obligation> {
        self.0.into_iter().map(Obligation)
    }
}

/// The open binding obligations of an equation instance (I2): the `\ceil(t)` factors its
/// binding obligations' decision left undecided, which the instance's result carries.
///
/// It has no `Default` and no constructor outside this module: its only source is
/// [`MatchedEquation::decide`], so an equation's result cannot be built without deciding its
/// bindings.
#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CarriedObligations(Vec<Obligation>);

impl CarriedObligations {
    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn into_predicates(self) -> Vec<Predicate> {
        self.0.into_iter().map(Obligation::into_predicate).collect()
    }
}

/// The conjuncts `C` a simplification `t = C ∧ t'` conjoins to its term, in the order they were
/// produced, each an obligation or an assumption (I4).
///
/// Obligations (the definedness of a term an equation binds or of an argument of an evaluated
/// hooked application, a refutation) conjoin to where `t'` exists. Assumptions (an applied
/// equation's open `ensures`) are what the definition asserts of that equation's result wherever
/// its instance exists, so they hold where the result's obligations hold and decide nothing about
/// existence. A successor keeps both kinds.
///
/// The role is recorded once, where the conjunct is produced (the constructors below), as an index
/// into the one conjunct list: no copy of the assumptions exists that a transformation of the list
/// could leave behind, and outside this module conjuncts join a result only as `Conjunct`s,
/// each of which carries its role.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResultConditions {
    conjuncts: Vec<Predicate>,
    /// Strictly ascending indices into `conjuncts` of the assumptions.
    assumptions: Vec<u32>,
}

impl ResultConditions {
    /// Every conjunct, in order: what a successor keeps.
    pub fn as_slice(&self) -> &[Predicate] {
        &self.conjuncts
    }

    pub fn is_empty(&self) -> bool {
        self.conjuncts.is_empty()
    }

    /// Every conjunct, in order, moved out.
    pub fn into_predicates(self) -> Vec<Predicate> {
        self.conjuncts
    }

    /// The conjuncts that decide whether the result exists: every conjunct equal to no
    /// assumption. An obligation equal to an assumption of the same result is discharged by it,
    /// because the assumption holds wherever the result's other obligations hold.
    pub fn obligations(&self) -> impl Iterator<Item = Obligation> + '_ {
        self.conjuncts
            .iter()
            .filter(|predicate| !self.asserts(predicate))
            .cloned()
            .map(Obligation)
    }

    /// Whether an assumption of this result equals `predicate`.
    pub fn asserts(&self, predicate: &Predicate) -> bool {
        self.assumptions
            .iter()
            .any(|&index| self.conjuncts[index as usize] == *predicate)
    }

    /// `\bottom`: the result's subject is empty. A refutation is an obligation.
    pub(crate) fn refuted() -> Self {
        Self {
            conjuncts: vec![Predicate::False],
            assumptions: Vec::new(),
        }
    }

    /// The argument definedness of an evaluated hooked application (I3). A hooked symbol is a
    /// function symbol and its application is strict, so a hook's value `v` for
    /// `f(t1, .., tn)` holds as `\ceil(t1) /\ .. /\ \ceil(tn) /\ v`; every member is an
    /// obligation. The obligations are computed here from the application
    /// (`simplify::hook_argument_definedness`, minus those in `known`), so a hook's result cannot
    /// carry an empty or a foreign list.
    pub(crate) fn hook_arguments(
        definition: &BackendDefinition,
        application: &Term,
        before_children: Option<&Term>,
        known: &[Predicate],
    ) -> Result<Self, crate::deferred::DeferredOutcome> {
        Ok(Self {
            conjuncts: hook_argument_definedness(definition, application, before_children, known)?,
            assumptions: Vec::new(),
        })
    }

    /// The conditions of an applied function equation's result, the only producer of
    /// assumptions.
    ///
    /// `ensures` is what the equation's instance leaves of its `ensures`, and `carried` its open
    /// binding obligations (I2). A `\bottom` among `ensures` (a refuted `ensures` or a bottom
    /// right-hand side) is the subject's own emptiness: the conjuncts are `ensures` alone, with no
    /// assumption and no binding obligation. Otherwise the open `ensures` are the assumptions, and
    /// the binding obligations not among them follow as obligations.
    pub(crate) fn equation(ensures: Vec<Predicate>, carried: CarriedObligations) -> Self {
        let mut conjuncts = ensures;
        if conjuncts.contains(&Predicate::False) {
            return Self {
                conjuncts,
                assumptions: Vec::new(),
            };
        }
        let assumptions = (0..conjuncts.len()).map(conjunct_index).collect();
        for predicate in carried.into_predicates() {
            if !conjuncts.contains(&predicate) {
                conjuncts.push(predicate);
            }
        }
        let conditions = Self {
            conjuncts,
            assumptions,
        };
        debug_assert!(conditions.assumptions_are_indices());
        conditions
    }

    /// The open binding obligations of a `\top` equation applied to an operand of a term-level
    /// `\and`: under `f(X) = \top`, `u /\ f(t)` is `u /\ \ceil(t)` (I2), and every member is an
    /// obligation.
    pub(crate) fn top_equation(obligations: Vec<Predicate>) -> Self {
        Self {
            conjuncts: obligations,
            assumptions: Vec::new(),
        }
    }

    /// `other`'s conjuncts after this result's, each keeping its role.
    #[cfg(test)]
    pub(crate) fn append(&mut self, other: Self) {
        let mut conjuncts = std::mem::take(self).into_conjuncts();
        conjuncts.extend(other.into_conjuncts());
        *self = Self::from_conjuncts(conjuncts);
    }

    /// The conjuncts in order, each with its role.
    pub(crate) fn into_conjuncts(self) -> Vec<Conjunct> {
        let mut assumptions = self.assumptions.into_iter().peekable();
        self.conjuncts
            .into_iter()
            .enumerate()
            .map(|(index, predicate)| Conjunct {
                predicate,
                assumption: assumptions
                    .next_if(|&assumption| assumption as usize == index)
                    .is_some(),
            })
            .collect()
    }

    /// The conditions of `conjuncts`, in order, each with its role.
    pub(crate) fn from_conjuncts(conjuncts: impl IntoIterator<Item = Conjunct>) -> Self {
        let mut conditions = Self::default();
        for (
            index,
            Conjunct {
                predicate,
                assumption,
            },
        ) in conjuncts.into_iter().enumerate()
        {
            conditions.conjuncts.push(predicate);
            if assumption {
                conditions.assumptions.push(conjunct_index(index));
            }
        }
        debug_assert!(conditions.assumptions_are_indices());
        conditions
    }

    /// The container invariant: the assumption indices ascend strictly and name conjuncts.
    fn assumptions_are_indices(&self) -> bool {
        self.assumptions.windows(2).all(|pair| pair[0] < pair[1])
            && self
                .assumptions
                .last()
                .is_none_or(|&last| (last as usize) < self.conjuncts.len())
    }
}

/// One conjunct of a [`ResultConditions`] with its role, the form in which a simplification
/// accumulates the conditions of its parts (`simplify::Log`): appending conjuncts keeps every
/// role without renumbering the assumptions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Conjunct {
    predicate: Predicate,
    /// Whether it is an assumption; otherwise it is an obligation.
    assumption: bool,
}

impl Conjunct {
    pub(crate) fn predicate(&self) -> &Predicate {
        &self.predicate
    }
}

impl IntoIterator for ResultConditions {
    type Item = Predicate;
    type IntoIter = std::vec::IntoIter<Predicate>;

    /// Every conjunct, in order (`into_predicates`).
    fn into_iter(self) -> Self::IntoIter {
        self.conjuncts.into_iter()
    }
}

fn conjunct_index(index: usize) -> u32 {
    u32::try_from(index).expect("a simplification result has fewer than 2^32 conjuncts")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Sort;

    /// The Boolean atom `name`, a predicate distinct from every other name's.
    fn atom(name: &str) -> Predicate {
        Predicate::Term(Term::variable(Variable::new(
            name,
            Sort::simple("SortBool"),
        )))
    }

    /// Open binding obligations, as `MatchedEquation::decide` leaves them.
    fn carried(predicates: Vec<Predicate>) -> CarriedObligations {
        CarriedObligations(predicates.into_iter().map(Obligation).collect())
    }

    fn obligations(conditions: &ResultConditions) -> Vec<Predicate> {
        conditions
            .obligations()
            .map(Obligation::into_predicate)
            .collect()
    }

    #[test]
    fn a_match_solution_states_its_conditions_under_its_substitution() {
        let sort = Sort::simple("SortInt");
        let x = Variable::new("X", sort.clone());
        let a = Term::variable(Variable::new("A", sort.clone()));
        let b = Term::variable(Variable::new("B", sort));
        let substitution = Substitution::from([(x.clone(), b.clone())]);
        let (kept, conditions) = MatchSolution::from_parts(
            substitution.clone(),
            vec![
                Predicate::Equals(Term::variable(x), a.clone()),
                atom("Free"),
            ],
        )
        .into_parts();
        assert_eq!(kept, substitution);
        assert_eq!(conditions, [Predicate::Equals(b, a), atom("Free")]);
    }

    #[test]
    fn binding_a_match_solution_restates_an_earlier_condition() {
        let sort = Sort::simple("SortInt");
        let x = Variable::new("X", sort.clone());
        let y = Variable::new("Y", sort.clone());
        let a = Term::variable(Variable::new("A", sort));
        let mut matched =
            MatchSolution::new(Substitution::from([(y.clone(), Term::variable(x.clone()))]));
        matched.conjoin([Predicate::Equals(Term::variable(y.clone()), a.clone())]);
        assert_eq!(
            matched.conditions(),
            [Predicate::Equals(Term::variable(x.clone()), a.clone())]
        );
        matched.bind(&Substitution::from([(x.clone(), a.clone())]));
        let (substitution, conditions) = matched.into_parts();
        assert_eq!(
            substitution,
            Substitution::from([(x, a.clone()), (y, a.clone())])
        );
        assert_eq!(conditions, [Predicate::Equals(a.clone(), a)]);
    }

    #[test]
    fn an_equation_result_records_its_ensures_as_assumptions_and_its_bindings_as_obligations() {
        let ensures = atom("Ensured");
        let obligation = atom("Defined");
        let mut conditions =
            ResultConditions::equation(vec![ensures.clone()], carried(vec![obligation.clone()]));
        assert_eq!(conditions.as_slice(), [ensures.clone(), obligation.clone()]);
        assert_eq!(obligations(&conditions), std::slice::from_ref(&obligation));
        assert!(conditions.asserts(&ensures));
        assert!(!conditions.asserts(&obligation));
        assert_eq!(conditions.assumptions, [0]);

        // A part without assumptions is appended after the conjuncts, and the assumption
        // indices stay as they are. Its obligation equal to the assumption is discharged by it.
        conditions.append(ResultConditions::top_equation(vec![
            ensures.clone(),
            atom("Bound"),
        ]));
        assert_eq!(
            conditions.as_slice(),
            [
                ensures.clone(),
                obligation.clone(),
                ensures.clone(),
                atom("Bound")
            ]
        );
        assert_eq!(conditions.assumptions, [0]);
        assert_eq!(
            obligations(&conditions),
            [obligation.clone(), atom("Bound")]
        );

        // A part with assumptions has its indices shifted past the conjuncts before it.
        conditions.append(ResultConditions::equation(
            vec![atom("Later")],
            carried(Vec::new()),
        ));
        assert_eq!(conditions.assumptions, [0, 4]);
        assert!(conditions.asserts(&atom("Later")));
        assert_eq!(obligations(&conditions), [obligation, atom("Bound")]);
    }

    #[test]
    fn an_equation_obligation_equal_to_its_ensures_is_not_restated() {
        let ensures = atom("Ensured");
        let conditions = ResultConditions::equation(
            vec![ensures.clone()],
            carried(vec![ensures.clone(), atom("Defined")]),
        );
        assert_eq!(conditions.as_slice(), [ensures, atom("Defined")]);
        assert_eq!(obligations(&conditions), [atom("Defined")]);
    }

    #[test]
    fn a_refuted_equation_result_has_no_assumption_and_no_binding_obligation() {
        let conditions = ResultConditions::equation(
            vec![atom("Ensured"), Predicate::False],
            carried(vec![atom("Defined")]),
        );
        assert_eq!(conditions.as_slice(), [atom("Ensured"), Predicate::False]);
        assert!(conditions.assumptions.is_empty());
        assert_eq!(
            obligations(&conditions),
            [atom("Ensured"), Predicate::False]
        );
        assert_eq!(ResultConditions::refuted().as_slice(), [Predicate::False]);
    }
}
