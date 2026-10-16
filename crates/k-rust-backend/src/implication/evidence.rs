//! Evidence tokens. A token exists only if the function that mints it established its premise.
//!
//! The fields are private to this module, so no other code, including the rest of
//! `implication`, can build a token except by calling its minting function (E0423). A token
//! states one fact about the instances of a pattern; the verdict that holds it asserts that
//! fact, and the minting function is the one place its premise is decided.

#![deny(clippy::wildcard_enum_match_arm)]

use rustc_hash::FxHashSet;
use std::sync::Arc;

use crate::{
    definedness::ceil_term,
    definition::BackendDefinition,
    rewrite::{Pattern, Truth, predicates_truth},
    rule::Predicate,
    simplify::normalize_predicate,
    smt::{Exactness, Satisfiability, SmtSolver, Validity, translation_exactness},
    stop::Stoppable,
    substitution::Substitution,
    term::{Term, TermKind},
};

use super::conjoin;

/// An instance of a pattern was shown: a valuation of its free variables, each over a sort the
/// definition shows inhabited, under which its constraints hold and its term denotes a value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Instance(());

impl Instance {
    /// Show that `pattern`, with `extra` conjoined to its constraints, has an instance.
    ///
    /// A term denotes a value exactly where `ceil_term` holds: it collects the definedness of
    /// partial applications, of set variables and of map keys and set elements being distinct;
    /// constructors, total functions, domain values and element variables always denote one.
    /// The exception is a conjunction of terms, which denotes a value only where both sides
    /// agree; such a term is not shown to have an instance. The remaining predicates must be
    /// true syntactically, or satisfiable by a solver `Sat` on a query whose translation is exact
    /// (`smt::translation_exactness`): an approximate `Sat` may come from an SMT model that is no
    /// K valuation.
    ///
    /// A pattern with a free variable denotes the union, over every value of the variable's
    /// sort, of what it denotes with the variable bound to that value; over an empty sort that
    /// union is empty, whatever the constraints say. Neither a syntactically true query nor a
    /// variable the query does not mention says anything about the variable's sort, so every
    /// free variable of the term and of the query must have a sort the definition shows
    /// inhabited ([`BackendDefinition::sort_is_inhabited`]). The `Int` and `Bool` variables an
    /// exact query may mention always are.
    ///
    /// `Err` is a stop of the solver's query: no answer exists, so whether an instance is shown
    /// is left to the caller's owner, never read as "not shown".
    pub(crate) fn shown(
        definition: &BackendDefinition,
        pattern: &Pattern,
        extra: &[Predicate],
        solver: &dyn SmtSolver,
    ) -> Stoppable<Option<Self>> {
        if contains_conjunction(&pattern.term) {
            return Ok(None);
        }
        let mut query = pattern.constraints.clone();
        let mut queried = query.iter().cloned().collect::<FxHashSet<_>>();
        // A term whose definedness depends on an impure application in an operand a conditional
        // never evaluates (`crate::deferred`) shows no instance.
        let Ok(term_definedness) = ceil_term(definition, &pattern.term) else {
            return Ok(None);
        };
        for predicate in extra.iter().cloned().chain(term_definedness) {
            if queried.insert(predicate.clone()) {
                query.push(predicate);
            }
        }
        if !pattern
            .term
            .attributes()
            .variables
            .iter()
            .cloned()
            .chain(query.iter().flat_map(Predicate::free_variables))
            .all(|variable| definition.sort_is_inhabited(&variable.sort))
        {
            return Ok(None);
        }
        let shown = predicates_truth(&query) == Truth::True
            || (translation_exactness(&query) == Exactness::Exact
                && matches!(
                    solver.is_sat(&query, &Substitution::new())?,
                    Ok(Satisfiability::Sat)
                ));
        Ok(shown.then_some(Self(())))
    }
}

/// Whether `term` contains a conjunction of terms, which denotes a value only where its two
/// sides agree.
fn contains_conjunction(term: &Term) -> bool {
    match term.kind() {
        TermKind::And(..) => true,
        TermKind::Application { arguments, .. } => arguments.iter().any(contains_conjunction),
        TermKind::Injection { term, .. } => contains_conjunction(term),
        TermKind::Map { entries, rest, .. } => {
            entries
                .iter()
                .any(|(key, value)| contains_conjunction(key) || contains_conjunction(value))
                || rest.as_ref().is_some_and(contains_conjunction)
        }
        TermKind::List { heads, rest, .. } => {
            heads.iter().any(contains_conjunction)
                || rest.as_ref().is_some_and(|(middle, tails)| {
                    contains_conjunction(middle) || tails.iter().any(contains_conjunction)
                })
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().any(contains_conjunction)
                || rest.as_ref().is_some_and(contains_conjunction)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => false,
    }
}

/// An instance of the antecedent outside the consequent was shown.
///
/// It is minted only inside `implication`, by the two functions that show such an instance, so
/// no other code can assert one. Fabricating a counterexample outside the crate does not compile:
///
/// ```compile_fail
/// use k_rust_backend::implication::Counterexample;
///
/// let _: Option<Counterexample> = Some(Counterexample(todo!()));
/// ```
///
/// Naming the type without constructing a value compiles:
///
/// ```
/// use k_rust_backend::implication::Counterexample;
///
/// let _: Option<Counterexample> = None;
/// ```
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Counterexample(Instance);

impl Counterexample {
    /// The instances of `antecedent` that `evidence` places outside the consequent, shown to
    /// exist.
    ///
    /// `Everywhere`: every instance of `antecedent` is outside, so one is shown by an instance
    /// of `antecedent` itself. `Where(o)`: the instances of `antecedent` that falsify `o` are
    /// outside, so one is shown by an instance of `antecedent ∧ ¬o`. `Err` is a stop of the
    /// solver's query ([`Instance::shown`]).
    pub(super) fn outside(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        evidence: &OutsideEvidence,
        solver: &dyn SmtSolver,
    ) -> Stoppable<Option<Self>> {
        let instance = match evidence {
            OutsideEvidence::Everywhere(everywhere) => match everywhere {
                Everywhere::TermMismatch
                | Everywhere::BottomConsequent
                | Everywhere::Refuted(ObligationRefuted(())) => {
                    Instance::shown(definition, antecedent, &[], solver)?
                }
            },
            OutsideEvidence::Where(obligations) => Instance::shown(
                definition,
                antecedent,
                &[normalize_predicate(Predicate::Not(Arc::new(conjoin(
                    obligations.clone(),
                ))))],
                solver,
            )?,
        };
        Ok(instance.map(Self))
    }

    /// `common` is the antecedent unified with the body `B` of a `\not B` consequent, with both
    /// sides' constraints and the bindings' definedness; an instance of it is an instance of the
    /// antecedent inside `B`, hence outside `\not B`. `Err` is a stop of the solver's query
    /// ([`Instance::shown`]).
    pub(super) fn common(
        definition: &BackendDefinition,
        common: &Pattern,
        solver: &dyn SmtSolver,
    ) -> Stoppable<Option<Self>> {
        Ok(Instance::shown(definition, common, &[], solver)?.map(Self))
    }
}

/// The obligation fails on every instance of the antecedent: a syntactic `false`, or a solver
/// `Refuted`.
///
/// It is minted only inside `implication`, from the simplifier's or the solver's answer.
/// Fabricating one outside the crate does not compile:
///
/// ```compile_fail
/// use k_rust_backend::implication::ObligationRefuted;
///
/// let _: Option<ObligationRefuted> = Some(ObligationRefuted(()));
/// ```
///
/// Naming the type without constructing a value compiles:
///
/// ```
/// use k_rust_backend::implication::ObligationRefuted;
///
/// let _: Option<ObligationRefuted> = None;
/// ```
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ObligationRefuted(());

impl ObligationRefuted {
    /// `Some` only for `Truth::False`: the obligation simplified to `false` holds on no
    /// valuation, hence on no instance of the antecedent.
    #[must_use]
    pub(super) fn by_simplifier(truth: Truth) -> Option<Self> {
        match truth {
            Truth::False => Some(Self(())),
            Truth::True | Truth::Unknown => None,
        }
    }

    /// `Some` only for `Validity::Refuted`: `known ∧ checked` is unsatisfiable, and `Unsat`
    /// refutes them, since both are definedness-explicit (docs/compatibility.md, "Solver
    /// decisions over partial operations").
    #[must_use]
    pub(super) fn by_solver(validity: &Validity) -> Option<Self> {
        match validity {
            Validity::Refuted => Some(Self(())),
            Validity::Valid
            | Validity::InconsistentGroundTruth
            | Validity::Contingent
            | Validity::Unknown(_) => None,
        }
    }

    /// The refutation of a disjunction of obligations, from one token per disjunct (a matched
    /// consequent branch, or the disjunction of the branches the per-branch check left
    /// undecided): a disjunction fails on an instance exactly when every disjunct does.
    ///
    /// `Some` only for a non-empty list: with no disjunct, no consequent matched, and there is
    /// no obligation to refute.
    #[must_use]
    pub(super) fn every_branch(branches: Vec<ObligationRefuted>) -> Option<Self> {
        (!branches.is_empty()).then_some(Self(()))
    }
}

/// What the check established about the antecedent's instances outside the consequent, for a
/// failing part the complete policy grades. A check that established nothing about them grades
/// to an indeterminate verdict without asking for a counterexample.
pub(super) enum OutsideEvidence {
    /// No instance of the antecedent is an instance of the consequent.
    Everywhere(Everywhere),
    /// The instances of the antecedent that falsify these obligations are outside the
    /// consequent, and the solver reported that some may exist. Its `Sat` may come from an
    /// approximate translation, so it is a candidate, not a witness.
    Where(Vec<Predicate>),
}

/// Why every instance of the antecedent is outside the consequent.
pub(super) enum Everywhere {
    /// The consequent's term does not match the antecedent's.
    TermMismatch,
    /// The consequent is `\bottom`, which has no instance.
    BottomConsequent,
    /// The antecedent's constraints refute the consequent's obligations.
    Refuted(ObligationRefuted),
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use super::*;

    #[test]
    fn a_simplifier_refutes_only_a_false_obligation() {
        assert!(ObligationRefuted::by_simplifier(Truth::False).is_some());
        assert!(ObligationRefuted::by_simplifier(Truth::True).is_none());
        assert!(ObligationRefuted::by_simplifier(Truth::Unknown).is_none());
    }

    #[test]
    fn a_solver_refutes_only_by_a_refuted_answer() {
        assert!(ObligationRefuted::by_solver(&Validity::Refuted).is_some());
        for validity in [
            Validity::Valid,
            Validity::InconsistentGroundTruth,
            Validity::Contingent,
            Validity::Unknown("timeout".to_owned()),
        ] {
            assert!(
                ObligationRefuted::by_solver(&validity).is_none(),
                "{validity:?}"
            );
        }
    }

    #[test]
    fn a_disjunction_is_refuted_only_with_at_least_one_refuted_disjunct() {
        assert!(ObligationRefuted::every_branch(Vec::new()).is_none());
        let refuted = ObligationRefuted::by_simplifier(Truth::False).expect("false is refuted");
        assert!(ObligationRefuted::every_branch(vec![refuted, refuted]).is_some());
    }
}
