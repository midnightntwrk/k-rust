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
//! Its only instance is an [`InstantiatedCondition`], whose predicates leave only with that
//! definedness stated ([`InstantiatedCondition::with_definedness`]) or through the condition's
//! simplification ([`InstantiatedCondition::simplify`]), which states it before anything but an
//! exact ground evaluation answers. A predicate derived from an instantiated condition therefore
//! reaches a solver or a decision only in definedness-explicit form.
//!
//! [`eliminate_bindings`] is the other half: eliminating a binding `x = t` of an element variable
//! keeps `\ceil(t)`.

use std::cell::Cell;

use crate::{
    definedness::{ceil_term, condition_definedness},
    definition::BackendDefinition,
    diagnostic,
    rewrite::{Truth, predicates_truth, substitute_predicates},
    rule::{Predicate, rename_predicates},
    simplify::SimplificationError,
    stop::Stoppable,
    substitution::Substitution,
    term::{TermKind, Variable, VariableKind},
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
        Self(substitute_predicates(&self.0, renaming))
    }

    /// Whether `predicate` is a conjunct of the instance as written: a binding's definedness
    /// that the instance already states is not restated beside it.
    pub(crate) fn contains(&self, predicate: &Predicate) -> bool {
        self.0.contains(predicate)
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
    ) -> Vec<Predicate> {
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
    /// the stop, on the outer layer: the attempt has no answer, and the general path would answer in
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
            return simplify(
                condition_definedness(definition, conditions, definedness_known),
                known,
                false,
            );
        }
        simplify(
            condition_definedness(definition, conditions, definedness_known),
            known,
            false,
        )
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
) -> Vec<Predicate> {
    let mut result = substitute_predicates(predicates, bindings);
    for (variable, value) in bindings {
        if variable.kind != VariableKind::Element || value.attributes().ceil_free() {
            continue;
        }
        for predicate in ceil_term(definition, value) {
            if !known.contains(&predicate) && !result.contains(&predicate) {
                result.push(predicate);
            }
        }
    }
    result
}
