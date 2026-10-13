//! ```toml algorithm
//! id = "backend.implication.check"
//! name = "subsumption by matching, witness elimination, and validity checking"
//! sites = ["check_established", "check_implication", "check_implication_with_existentials",
//!     "check_implication_with_existentials_and_options",
//!     "check_implication_with_existentials_complete",
//!     "check_disjunctive_implication_with_existentials", "eliminate_existential_witnesses"]
//! variable = "r = antecedent simplification rounds; c = consequents"
//! counters = ["SmtQueries"]
//! span = "per problem"
//! consumes = [
//!   { type = "k_rust_backend::matching::MatchResult", role = "match result" },
//!   { type = "k_rust_backend::substitution::Substitution", role = "extracted substitution" },
//! ]
//!
//! [[cost]]
//! mode = "one consequent (check_established)"
//! bound = """\
//! O(r) matching problems and antecedent simplifications, then one discharge with one \
//! check_predicates (up to three solver subqueries) and up to four is_sat queries (the third, \
//! after one simplification of the antecedent's knowledge, only when a matched consequent is \
//! refuted, undecided or unprepared, empty_unless_consistent; the fourth only when the complete \
//! policy grades a failing part, grade_outside), and, when the complete policy grades a term \
//! mismatch it shows no instance outside of, one more simplification of the antecedent's \
//! knowledge and up to two more is_sat queries (antecedent_is_empty)"""
//!
//! [[cost]]
//! mode = "several consequents (check_disjunctive_implication_with_existentials)"
//! bound = """\
//! O(r x (c matching problems + c witness eliminations + one check_predicates)), then one \
//! simplification of the antecedent's knowledge and one is_sat query when a matched consequent is \
//! refuted, undecided or unprepared (empty_unless_consistent)"""
//! ```
//!
//! Subsumption by Implies-mode matching, existential witness elimination, and SMT validity of
//! the residual, iterated to a fixed point of the simplified antecedent (Kore checkImplication):
//! O(rounds x (|consequents| x one matching problem + witness saturation + one SMT validity));
//! one `Counter::SmtQueries` per solver call (an antecedent satisfiability check, up to three
//! validity subqueries for the residual, a refutation check, and, for a match refuted, undecided
//! or unprepared, a satisfiability check of the antecedent's knowledge),
//! `Counter::ProofImplicationChecks` at the caller.
//!
//! The check is policy-neutral: it records what it established about the antecedent's
//! instances (`Established`), and each policy grades that value once. The proof policy asks
//! which instances of a proof state lie in the destination and answers a [`Coverage`]
//! (`grade_coverage`); the complete policy asks whether every instance of the antecedent lies in
//! the consequent and answers an [`ImplicationVerdict`] (`grade_verdict`), whose `Invalid` holds
//! a [`Counterexample`]. The wire vocabulary ([`ImplicationStatus`], [`ImplicationFailure`],
//! [`ImplicationCondition`]) is derived from a verdict, never stored.

#![deny(clippy::wildcard_enum_match_arm)]

use std::{collections::BTreeSet, error::Error, fmt};

use k_rust_kore::kore::ast as kore;
use k_rust_kore::measure::{self, Algorithm};

mod consequent;
mod destination;
mod evidence;

use consequent::{ConsequentMatch, ConsequentObligations};
use destination::Destination;
pub(crate) use evidence::Instance;
pub use evidence::{Counterexample, ObligationRefuted};
use evidence::{Everywhere, OutsideEvidence};

use crate::{
    condition::{eliminate_bindings, instantiate_constraints},
    definedness::{ceil_term, pattern_knowledge},
    definition::{Admitted, BackendDefinition},
    fresh::{RequestNames, fresh_name_apart},
    ite::{IteSplit, split_ite_pair},
    matching::{
        FailReason, MatchMode, MatchResult, SortError, is_collection_term,
        match_terms_in_definition, merge_free_parts, solve_collection_pairs_in_definition,
    },
    rewrite::{Pattern, Truth, predicates_truth, substitute_predicates},
    rule::Predicate,
    simplify::{
        SimplificationError, SimplificationOptions, normalize_predicate,
        simplify_predicates_with_solver, simplify_with_solver,
    },
    smt::{Satisfiability, SmtSolver, Validity},
    stop::{Layered, Stoppable, Unwind},
    substitution::{Substitution, compose, extract_substitution_for, substitute},
    term::Variable,
    term::names::FreshMarker,
    unification::{Unification, UnificationResult, unify_term_pairs},
};

/// The wire status of an [`ImplicationVerdict`] ([`ImplicationVerdict::status`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImplicationStatus {
    Valid,
    Invalid,
    Indeterminate,
}

/// Which part of the consequent the antecedent's outside instances fail, as the wire reports it
/// ([`ImplicationVerdict::failure`], from [`Outside`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImplicationFailure {
    TermMismatch,
    PartialCoverage,
    ConsequentCondition,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Side {
    Antecedent,
    Consequent,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ImplicationRequestError {
    MacroOrAlias {
        side: Side,
        name: String,
    },
    NonFunctionLikeAntecedent,
    NonSingletonConsequent,
    ExistentialCapture {
        captured: Vec<String>,
        existentials: Vec<String>,
    },
    SortMismatch {
        antecedent: kore::Sort,
        consequent: kore::Sort,
    },
}

/// Validate the syntactic request ladder before either side is internalized.
pub fn validate_request(
    definition: &BackendDefinition,
    antecedent: &kore::Pattern,
    consequent: &kore::Pattern,
) -> Result<(), ImplicationRequestError> {
    for (side, pattern) in [
        (Side::Antecedent, antecedent),
        (Side::Consequent, consequent),
    ] {
        if let Err(crate::definition::DefinitionError::MacroOrAliasInImplication(name)) =
            definition.validate_implication_pattern(pattern)
        {
            return Err(ImplicationRequestError::MacroOrAlias { side, name });
        }
    }

    let antecedent_body = antecedent.strip_exists();
    if matches!(antecedent_body, kore::Pattern::Or { arguments, .. } if arguments.len() != 1)
        || matches!(
            antecedent_body,
            kore::Pattern::Top { .. } | kore::Pattern::Mu { .. } | kore::Pattern::Nu { .. }
        )
    {
        return Err(ImplicationRequestError::NonFunctionLikeAntecedent);
    }

    let consequent_body = consequent.strip_exists();
    if matches!(consequent_body, kore::Pattern::Or { arguments, .. } if arguments.len() != 1) {
        return Err(ImplicationRequestError::NonSingletonConsequent);
    }

    let antecedent_free = antecedent.free_variables();
    let (_, existentials) = consequent.leading_existentials();
    let captured = existentials
        .iter()
        .filter(|variable| antecedent_free.contains(*variable))
        .map(|variable| variable.name.clone())
        .collect::<Vec<_>>();
    if !captured.is_empty() {
        return Err(ImplicationRequestError::ExistentialCapture {
            captured,
            existentials: existentials
                .into_iter()
                .map(|variable| variable.name.clone())
                .collect(),
        });
    }

    if let (Some(antecedent_sort), Some(consequent_sort)) =
        (antecedent.syntactic_sort(), consequent.syntactic_sort())
        && antecedent_sort != consequent_sort
    {
        return Err(ImplicationRequestError::SortMismatch {
            antecedent: antecedent_sort.clone(),
            consequent: consequent_sort.clone(),
        });
    }
    Ok(())
}

/// The verdict for a `\bottom` antecedent (after its leading existentials), which has no
/// instance and so implies anything: [`ImplicationVerdict::VacuouslyValid`]. `None` for every
/// other antecedent.
///
/// Callers test this before internalizing the antecedent, and route the consequent with
/// [`special_consequent`] only for an antecedent this returns `None` for.
pub fn bottom_antecedent(antecedent: &kore::Pattern) -> Option<ImplicationVerdict> {
    matches!(antecedent.strip_exists(), kore::Pattern::Bottom { .. })
        .then_some(ImplicationVerdict::VacuouslyValid)
}

/// A consequent whose syntax routes the check, for an antecedent that is not `\bottom`
/// ([`bottom_antecedent`]). None of them is a verdict: each names the one way it is decided.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SpecialConsequent {
    /// `\top` contains every value: the caller answers [`ImplicationVerdict::Valid`] with no
    /// binding.
    Top,
    /// `\bottom` contains no value: graded by [`grade_bottom_consequent`].
    Bottom,
    /// `\not C`: decided by [`check_negated_consequent`].
    Not,
}

/// Route a consequent by its syntax (after its leading existentials): `None` for a consequent
/// that the matching check decides.
///
/// It takes no definition and no solver, so it cannot mint a [`Counterexample`]; the invalid
/// answers of the routed cases come from [`grade_bottom_consequent`] and
/// [`check_negated_consequent`].
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "KorePattern is syntax; only the listed variants are special here"
)]
pub fn special_consequent(consequent: &kore::Pattern) -> Option<SpecialConsequent> {
    match consequent.strip_exists() {
        kore::Pattern::Top { .. } => Some(SpecialConsequent::Top),
        kore::Pattern::Bottom { .. } => Some(SpecialConsequent::Bottom),
        kore::Pattern::Not { .. } => Some(SpecialConsequent::Not),
        _ => None,
    }
}

/// Grade `A -> \bottom` on the internalized antecedent `A`.
///
/// `\bottom` has no instance, so every instance of the antecedent lies outside it: the
/// implication is invalid exactly when the antecedent has an instance, and holds vacuously
/// otherwise. The answer is `Invalid` only when a [`Counterexample`] shows that instance, and
/// `VacuouslyValid` only when the antecedent is shown to have none (`antecedent_is_empty`):
/// its constraints are contradictory, or they contradict the definedness of the term or of
/// their own atoms. `M Map (1 |-> 2)` under `¬(1 in_keys M = false)` is such an antecedent:
/// the concatenation is defined only where `1` is not a key of `M`, and the constraint keeps
/// the other valuations. Otherwise the answer is `Indeterminate`. `Invalid` and `Indeterminate`
/// report the consequent's condition as refuted. `Err` is a stop of a solver query: there is no
/// verdict.
pub fn grade_bottom_consequent(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    solver: &dyn SmtSolver,
) -> Stoppable<ImplicationVerdict> {
    grade_outside(
        definition,
        antecedent,
        Outside::ConsequentCondition(MatchReport::refuted(Bindings::default())),
        OutsideEvidence::Everywhere(Everywhere::BottomConsequent),
        Emptiness::Undecided,
        solver,
    )
}

/// Whether `antecedent` is shown to have no instance: its constraints are syntactically false or
/// the solver answers `Unsat` for them, or its knowledge, which adds the definedness of the term
/// and of the constraints' atoms, is contradictory (`knowledge_is_contradictory`). Every instance
/// satisfies both sets of facts (I7), and an `Unsat` answer refutes whatever the translation
/// approximated, so either contradiction leaves none.
fn antecedent_is_empty(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<bool> {
    if predicates_truth(&antecedent.constraints) == Truth::False
        || matches!(
            solver.is_sat(&antecedent.constraints, &Substitution::new())?,
            Ok(Satisfiability::Unsat)
        )
    {
        return Ok(true);
    }
    knowledge_is_contradictory(
        definition,
        &pattern_knowledge(definition, antecedent),
        options,
        solver,
    )
}

/// Check `A -> \not C`, the consequent [`special_consequent`] routes here.
///
/// Under the universal closure of the free variables of both sides, `A -> \not C` holds exactly
/// when no valuation gives `A` and `C` a common value, that is when the pattern `A /\ C` is
/// empty. The terms of `A` and `C` are unified with their shared variables denoting the same
/// value; the existentials of either side are renamed apart from the other's free variables
/// first, because `(\exists E. A) /\ C` is `\exists E. (A /\ C)` for `E` not free in `C`.
/// - A unification clash (different constructors, values or sorts, or an occurs cycle below
///   constructors), or constraints that with the definedness of the unified term and bindings
///   are refuted by the solver (`Unsat` is sound under every approximation) or contradictory once
///   simplified (`knowledge_is_contradictory`), show `A /\ C` empty: `Valid` with no binding. An
///   empty `A` is one such case.
/// - A unifier whose instance of `A` with both sides' constraints is shown to have an instance
///   (a [`Counterexample`]) is a common value: `Invalid`, with no [`Outside`] report, since the
///   counterexample lies inside `C` rather than failing a part of it.
/// - Anything else, including a collection unification left unsupported and a consequent
///   `\exists E. \not C` (which asks for `C` to fail for some `E` rather than for all), is
///   `Indeterminate` with no report.
///
/// The consequent arrives admitted by the caller ([`Admitted`]): the argument of its `\not` is
/// internalized by the definition that admitted it, under the sort variables it was admitted
/// under, which must be `definition`.
///
/// `Ok(Err)` reports a consequent that does not internalize; `Err` is a stop of a solver query,
/// for which there is no verdict.
pub fn check_negated_consequent(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    antecedent_existentials: &BTreeSet<Variable>,
    consequent: Admitted<'_>,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<ImplicationVerdict, crate::definition::DefinitionError>> {
    debug_assert!(
        std::ptr::eq(consequent.definition(), definition),
        "the consequent is admitted against the definition that checks the implication"
    );
    let kore::Pattern::Not { argument, .. } = consequent.pattern() else {
        return Ok(Ok(ImplicationVerdict::Indeterminate { outside: None }));
    };
    let (negated, negated_existentials) = match consequent
        .definition()
        .internalize_implication_pattern(argument, consequent.sort_variables())
    {
        Ok(internalized) => internalized,
        Err(error) => return Ok(Err(error)),
    };
    let renamed = rename_existentials_apart(antecedent, antecedent_existentials, &negated);
    let antecedent = renamed.as_ref().unwrap_or(antecedent);
    let renamed = rename_existentials_apart(&negated, &negated_existentials, antecedent);
    let negated = renamed.as_ref().unwrap_or(&negated);
    let unification = unify_term_pairs(
        definition,
        Substitution::new(),
        [(antecedent.term.clone(), negated.term.clone())],
    );
    let Unification {
        substitution,
        constraints,
    } = match unification {
        UnificationResult::Bottom(_) => {
            return Ok(Ok(ImplicationVerdict::Valid(Bindings::default())));
        }
        UnificationResult::Unsupported { .. } => {
            return Ok(Ok(ImplicationVerdict::Indeterminate { outside: None }));
        }
        UnificationResult::Unified(unification) => unification,
    };
    // Each side's constraints and the unifier's are conditions on the common instances, stated
    // with their definedness (I1): an atom over a term undefined somewhere is `⊥` there, and under
    // a negation `⊤`, which a solver reading a partial function as a total operation would not see.
    let mut conjunction = Pattern {
        term: substitute(&antecedent.term, &substitution),
        constraints: instantiate_constraints(&antecedent.constraints, &substitution)
            .with_definedness(definition, &[]),
    };
    // The bindings' values must denote values too, even where the term no longer mentions them.
    let definedness = substitution
        .values()
        .flat_map(|value| ceil_term(definition, value))
        .collect::<Vec<_>>();
    for predicate in instantiate_constraints(&negated.constraints, &substitution)
        .with_definedness(definition, &conjunction.constraints)
        .into_iter()
        .chain(
            instantiate_constraints(&constraints, &substitution)
                .with_definedness(definition, &conjunction.constraints),
        )
        .chain(definedness)
    {
        if !conjunction.constraints.contains(&predicate) {
            conjunction.constraints.push(predicate);
        }
    }
    if let Some(counterexample) = Counterexample::common(definition, &conjunction, solver)? {
        return Ok(Ok(ImplicationVerdict::Invalid {
            counterexample,
            outside: None,
        }));
    }
    let mut query = conjunction.constraints.clone();
    for predicate in ceil_term(definition, &conjunction.term) {
        if !query.contains(&predicate) {
            query.push(predicate);
        }
    }
    // The query is the knowledge of `A /\ C`: its constraints with their atoms' definedness, the
    // bindings' and the term's. The solver reads it as written first; only when that leaves it
    // open is it simplified and decided again (`knowledge_is_contradictory`), since the
    // simplifier evaluates what the solver reads as opaque atoms (a `\ceil` of a collection, say).
    if predicates_truth(&query) == Truth::False
        || matches!(
            solver.is_sat(&query, &Substitution::new())?,
            Ok(Satisfiability::Unsat)
        )
        || knowledge_is_contradictory(definition, &query, SimplificationOptions::default(), solver)?
    {
        return Ok(Ok(ImplicationVerdict::Valid(Bindings::default())));
    }
    Ok(Ok(ImplicationVerdict::Indeterminate { outside: None }))
}

/// The wire record of a verdict's condition ([`ImplicationVerdict::into_condition`]).
///
/// An empty predicate list denotes `top`. A vacuous verdict carries `false`: the antecedent has
/// no instance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ImplicationCondition {
    pub predicates: Vec<Predicate>,
    pub substitution: Substitution,
    /// Existential bindings recovered from residual implication obligations.
    ///
    /// These are kept separate from the term-match substitution because the KORE RPC wire only
    /// reports the latter.
    pub witnesses: Substitution,
}

/// The bindings a match of the consequent produced.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Bindings {
    /// The term match's substitution for the consequent's variables.
    pub substitution: Substitution,
    /// Existential witnesses recovered from residual obligations.
    pub witnesses: Substitution,
}

impl From<Bindings> for ImplicationCondition {
    /// The condition of a match that holds everywhere: its bindings and no predicate.
    fn from(bindings: Bindings) -> Self {
        Self {
            predicates: Vec::new(),
            substitution: bindings.substitution,
            witnesses: bindings.witnesses,
        }
    }
}

/// The part of the antecedent that lies in the consequent: its instances that satisfy the
/// obligations of a match of the consequent against it.
///
/// Every instance that satisfies the obligations is inside the consequent by construction,
/// whatever a solver says about them, so the complement of [`CoverageCondition::covered`] is the
/// rest of the antecedent. When the antecedent is a variable `X` and one obligation is an
/// equation `X = t`, the wire reports that binding in the substitution
/// ([`CoverageCondition::to_condition`]); it stays one of the obligations the covered instances
/// satisfy, so `covered` keeps it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoverageCondition {
    /// Every obligation the covered instances satisfy, in the order the check stated them.
    obligations: Vec<Predicate>,
    /// The obligation that binds the antecedent's variable, reported as a binding on the wire.
    antecedent_binding: Option<AntecedentBinding>,
    bindings: Bindings,
}

/// An obligation `X = t` (or `t = X`) that binds the antecedent's variable `X` to a value `t`
/// that does not mention it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct AntecedentBinding {
    /// Its position among the obligations.
    position: usize,
    variable: Variable,
    value: crate::term::Term,
}

impl CoverageCondition {
    /// The coverage condition of a match whose remainder obligations are `obligations`.
    ///
    /// The first obligation that binds `antecedent_variable` is recorded as the antecedent's
    /// binding, unless the match already binds that variable.
    fn partial(
        antecedent_variable: Option<&Variable>,
        bindings: Bindings,
        obligations: Vec<Predicate>,
    ) -> Self {
        let antecedent_binding = antecedent_variable
            .filter(|variable| !bindings.substitution.contains_key(*variable))
            .and_then(|_| {
                obligations
                    .iter()
                    .enumerate()
                    .find_map(|(position, obligation)| {
                        let Predicate::Equals(left, right) = obligation else {
                            return None;
                        };
                        implication_binding(left, right, antecedent_variable)
                            .or_else(|| implication_binding(right, left, antecedent_variable))
                            .map(|(variable, value)| AntecedentBinding {
                                position,
                                variable: variable.clone(),
                                value: value.clone(),
                            })
                    })
            });
        Self {
            obligations,
            antecedent_binding,
            bindings,
        }
    }

    /// The coverage condition of obligations that hold on part of the antecedent: no binding is
    /// recorded, and the wire reports every obligation as a predicate.
    fn contingent(bindings: Bindings, obligations: Vec<Predicate>) -> Self {
        Self {
            obligations,
            antecedent_binding: None,
            bindings,
        }
    }

    /// The predicate that holds exactly on the covered part: the conjunction of every
    /// obligation, the antecedent's binding included. Its complement is the part of the
    /// antecedent outside the consequent.
    pub fn covered(&self) -> Predicate {
        conjoin(self.obligations.clone())
    }

    /// The wire record: the antecedent's binding is reported in the substitution and the other
    /// obligations as predicates.
    pub fn to_condition(&self) -> ImplicationCondition {
        self.clone().into_condition()
    }

    fn into_condition(self) -> ImplicationCondition {
        let Self {
            mut obligations,
            antecedent_binding,
            bindings:
                Bindings {
                    mut substitution,
                    witnesses,
                },
        } = self;
        if let Some(binding) = antecedent_binding {
            obligations.remove(binding.position);
            substitution.insert(binding.variable, binding.value);
        }
        ImplicationCondition {
            predicates: obligations,
            substitution,
            witnesses,
        }
    }
}

#[cfg(test)]
impl CoverageCondition {
    /// The coverage condition of `obligations` with no binding, for the tests of its consumers.
    pub(crate) fn of_obligations(obligations: Vec<Predicate>) -> Self {
        Self::contingent(Bindings::default(), obligations)
    }
}

/// The matcher's report beside a failing consequent condition (refuted, or failing on part of
/// the antecedent): the match's bindings and the predicates reported with them.
///
/// It describes no part of the antecedent and has no complement: beside bindings its predicates
/// are empty, which does not mean that every instance lies in the consequent.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MatchReport(ImplicationCondition);

impl MatchReport {
    /// The report of a refuted condition: the match's bindings, or, when the match bound
    /// nothing, the refuted condition itself as `false`.
    fn refuted(bindings: Bindings) -> Self {
        let predicates = if bindings.substitution.is_empty() && bindings.witnesses.is_empty() {
            vec![Predicate::False]
        } else {
            Vec::new()
        };
        Self(ImplicationCondition {
            predicates,
            substitution: bindings.substitution,
            witnesses: bindings.witnesses,
        })
    }

    /// The report of a condition that fails on part of the antecedent: the match's bindings.
    fn contingent(bindings: Bindings) -> Self {
        Self(bindings.into())
    }

    /// The wire record of the report.
    pub fn condition(&self) -> &ImplicationCondition {
        &self.0
    }
}

/// The proof policy's answer: which instances of a proof state lie in the destination.
///
/// Each variant carries exactly the evidence it asserts: a refuted part holds an
/// [`ObligationRefuted`], and only a [`CoverageCondition`] describes a covered part whose
/// complement is the rest of the state. A matcher's report beside a refuted condition is a
/// [`MatchReport`], so it cannot be complemented as if it were a coverage condition:
///
/// ```compile_fail
/// use k_rust_backend::implication::{Coverage, CoverageCondition};
///
/// fn complement(_covered: &CoverageCondition) {}
///
/// fn uncovered(coverage: &Coverage) {
///     match coverage {
///         Coverage::ConditionRefuted { report, .. }
///         | Coverage::PartialCoverage {
///             coverage: report, ..
///         } => complement(report),
///         _ => {}
///     }
/// }
/// ```
///
/// Complementing the coverage condition of a partial coverage compiles:
///
/// ```
/// use k_rust_backend::implication::{Coverage, CoverageCondition};
///
/// fn complement(_covered: &CoverageCondition) {}
///
/// fn uncovered(coverage: &Coverage) {
///     match coverage {
///         Coverage::PartialCoverage {
///             coverage: report, ..
///         } => complement(report),
///         _ => {}
///     }
/// }
/// ```
///
/// A refuted part needs its refutation, which no code outside the check can mint, so an
/// undecided solver answer cannot be graded as one:
///
/// ```compile_fail
/// use k_rust_backend::{
///     implication::{Coverage, CoverageCondition, ObligationRefuted},
///     smt::Validity,
/// };
///
/// fn grade(coverage: CoverageCondition, validity: Validity) -> Coverage {
///     match validity {
///         Validity::Unknown(_) => Coverage::PartialCoverage {
///             coverage,
///             refuted: ObligationRefuted(()),
///         },
///         _ => Coverage::Undecided,
///     }
/// }
/// ```
///
/// Grading it with a refutation the caller holds compiles:
///
/// ```
/// use k_rust_backend::{
///     implication::{Coverage, CoverageCondition, ObligationRefuted},
///     smt::Validity,
/// };
///
/// fn grade(coverage: CoverageCondition, validity: Validity, refuted: ObligationRefuted) ->
/// Coverage {
///     match validity {
///         Validity::Unknown(_) => Coverage::PartialCoverage { coverage, refuted },
///         _ => Coverage::Undecided,
///     }
/// }
/// ```
#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Coverage {
    /// Every instance of the state lies in the destination.
    Covered(Bindings),
    /// The state has no instance.
    Vacuous,
    /// The destination's term does not match the state's: no instance lies in the destination.
    TermMismatch,
    /// The destination's condition is refuted on every instance of the state.
    ConditionRefuted {
        report: MatchReport,
        refuted: ObligationRefuted,
    },
    /// A match remainder's obligation is refuted on every instance of the state; `coverage` is
    /// the covered part, and its complement is outside the destination.
    PartialCoverage {
        coverage: CoverageCondition,
        refuted: ObligationRefuted,
    },
    /// Neither the obligation nor its negation is refuted: `coverage` is inside the destination,
    /// and its complement is not known to be outside.
    Contingent(CoverageCondition),
    /// Nothing was established.
    Undecided,
}

/// Which part of the consequent the antecedent's outside instances fail, as the wire reports it
/// ([`ImplicationFailure`]). It asserts nothing about whether they exist; the verdict does.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Outside {
    /// The consequent's term does not match the antecedent's.
    TermMismatch,
    /// The consequent's condition is refuted, or (for a contingent answer) fails on part of the
    /// antecedent.
    ConsequentCondition(MatchReport),
    /// A match remainder's obligation fails; the condition is the part of the antecedent that
    /// would lie in the consequent.
    PartialCoverage(CoverageCondition),
}

impl Outside {
    fn failure(&self) -> ImplicationFailure {
        match self {
            Self::TermMismatch => ImplicationFailure::TermMismatch,
            Self::ConsequentCondition(_) => ImplicationFailure::ConsequentCondition,
            Self::PartialCoverage(_) => ImplicationFailure::PartialCoverage,
        }
    }

    fn into_condition(self) -> Option<ImplicationCondition> {
        match self {
            Self::TermMismatch => None,
            Self::ConsequentCondition(report) => Some(report.0),
            Self::PartialCoverage(coverage) => Some(coverage.into_condition()),
        }
    }
}

/// The complete policy's answer to "does every instance of the antecedent lie in the
/// consequent?"
///
/// `Invalid` asserts an instance of the antecedent outside the consequent, so it holds a
/// [`Counterexample`], which only the check can mint; a verdict built outside it cannot claim
/// one:
///
/// ```compile_fail
/// use k_rust_backend::implication::{Counterexample, ImplicationVerdict};
///
/// fn verdict() -> ImplicationVerdict {
///     ImplicationVerdict::Invalid {
///         counterexample: Counterexample(todo!()),
///         outside: None,
///     }
/// }
/// ```
///
/// Reading an `Invalid` verdict compiles:
///
/// ```
/// use k_rust_backend::implication::ImplicationVerdict;
///
/// fn is_invalid(verdict: &ImplicationVerdict) -> bool {
///     matches!(verdict, ImplicationVerdict::Invalid { counterexample: _, .. })
/// }
/// ```
#[must_use]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ImplicationVerdict {
    /// Every instance of the antecedent lies in the consequent under these bindings.
    Valid(Bindings),
    /// The antecedent has no instance.
    VacuouslyValid,
    /// An instance of the antecedent outside the consequent was shown. `outside` names the part
    /// of the consequent it fails; it is `None` for a `\not` consequent.
    Invalid {
        counterexample: Counterexample,
        outside: Option<Outside>,
    },
    /// Neither answer was established. `outside` names the part of the consequent the
    /// antecedent's instances fail, if they have any.
    Indeterminate { outside: Option<Outside> },
}

impl ImplicationVerdict {
    /// The wire status.
    pub fn status(&self) -> ImplicationStatus {
        match self {
            Self::Valid(_) | Self::VacuouslyValid => ImplicationStatus::Valid,
            Self::Invalid { .. } => ImplicationStatus::Invalid,
            Self::Indeterminate { .. } => ImplicationStatus::Indeterminate,
        }
    }

    /// The wire failure: the part of the consequent the outside instances fail.
    pub fn failure(&self) -> Option<ImplicationFailure> {
        match self {
            Self::Valid(_) | Self::VacuouslyValid => None,
            Self::Invalid { outside, .. } | Self::Indeterminate { outside } => {
                outside.as_ref().map(Outside::failure)
            }
        }
    }

    /// The wire condition: the bindings of a valid match, `false` for a vacuous one, and the
    /// report or coverage condition of a failing part.
    pub fn into_condition(self) -> Option<ImplicationCondition> {
        match self {
            Self::Valid(bindings) => Some(bindings.into()),
            Self::VacuouslyValid => Some(ImplicationCondition {
                predicates: vec![Predicate::False],
                substitution: Substitution::new(),
                witnesses: Substitution::new(),
            }),
            Self::Invalid { outside, .. } | Self::Indeterminate { outside } => {
                outside.and_then(Outside::into_condition)
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Obligations {
    predicates: Vec<Predicate>,
    witnesses: Substitution,
}

/// What the check established about the antecedent's instances, before a policy grades it.
/// Each variant carries exactly the evidence its name asserts.
enum Established {
    /// Every instance satisfies the obligations under these bindings.
    Holds(Bindings),
    /// The antecedent has no instance.
    AntecedentEmpty,
    /// The consequent's term does not match the antecedent's.
    TermMismatch,
    /// The obligations fail on every instance.
    Refuted {
        refuted: ObligationRefuted,
        by: Refuter,
        origin: Origin,
        bindings: Bindings,
        obligations: Vec<Predicate>,
    },
    /// Neither the obligations nor their negation is refuted.
    Contingent {
        origin: Origin,
        bindings: Bindings,
        obligations: Vec<Predicate>,
    },
    /// Nothing about the obligations was established.
    Undecided {
        origin: Origin,
        bindings: Bindings,
        obligations: Vec<Predicate>,
    },
    /// Nothing was established and no obligation is at hand: preparing the obligations
    /// (witness elimination or simplification) failed.
    Unprepared,
}

/// Which procedure refuted the obligations.
#[derive(Clone, Copy)]
enum Refuter {
    Simplifier,
    Solver,
}

/// Whether the obligations include equations of a match remainder, that is whether the
/// consequent's term matched only under them.
#[derive(Clone, Copy)]
enum Origin {
    ConsequentCondition,
    MatchRemainder,
}

/// What the policy-neutral check returns: the established value and the antecedent it was
/// established on (the last round's simplified antecedent).
struct Checked {
    established: Established,
    antecedent: Pattern,
    /// The antecedent's variable, when its term is one.
    antecedent_variable: Option<Variable>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ImplicationError {
    Subsorting(SortError),
    Simplification(SimplificationError),
}

impl fmt::Display for ImplicationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Subsorting(error) => write!(formatter, "{error}"),
            Self::Simplification(error) => write!(formatter, "{error}"),
        }
    }
}

impl Error for ImplicationError {}

/// The result of a check inside this module: `?` propagates a stop and a failure alike. Every
/// entry point returns it layered ([`Layered::layered`]): the stop outside, the failure inside.
type CheckResult<T> = Result<T, Unwind<ImplicationError>>;

/// Check an implication under the proof policy: which instances of `antecedent` lie in
/// `consequent` ([`Coverage`]).
///
/// Like every check of this module, the result has two layers: the outer `Err` is a
/// [`Stop`](crate::stop::Stop) (the request was cancelled, the step deadline passed, the solver's
/// prelude failed, or the thread's stack ran low), for which the check has no verdict; the inner
/// `Result` is the verdict or the check's failure. No verdict, not even an undecided one, stands
/// in for a stop.
pub fn check_implication(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    consequent: &Pattern,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Coverage, ImplicationError>> {
    check_implication_with_existentials_and_options(
        definition,
        antecedent,
        &BTreeSet::new(),
        consequent,
        &BTreeSet::new(),
        SimplificationOptions::default(),
        solver,
    )
}

/// [`check_implication`] with the existentials of both sides.
pub fn check_implication_with_existentials(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    antecedent_existentials: &BTreeSet<Variable>,
    consequent: &Pattern,
    consequent_existentials: &BTreeSet<Variable>,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Coverage, ImplicationError>> {
    check_implication_with_existentials_and_options(
        definition,
        antecedent,
        antecedent_existentials,
        consequent,
        consequent_existentials,
        SimplificationOptions::default(),
        solver,
    )
}

/// Check an implication under the complete policy: does every instance of `antecedent` lie in
/// `consequent` ([`ImplicationVerdict`])?
///
/// A refutation of the obligations, and an answer where both the obligations and their negation
/// are satisfiable under the antecedent, each place instances of the antecedent outside the
/// consequent, if it has any. `Invalid` asserts such an instance, so it holds a
/// [`Counterexample`] (`grade_verdict`): a refutation needs an instance of the antecedent, and a
/// contingent answer an instance of the antecedent with the negated obligations, each shown
/// syntactically or by an exact solver `Sat`. Without that instance the implication may hold
/// vacuously. The check has already answered `VacuouslyValid` where it showed the antecedent
/// empty while deciding obligations (`empty_unless_consistent`); a term mismatch decided none, so
/// its grading decides the emptiness (`grade_outside`). Any other answer without an instance is
/// `Indeterminate` with the same report.
pub fn check_implication_with_existentials_complete(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    antecedent_existentials: &BTreeSet<Variable>,
    consequent: &Pattern,
    consequent_existentials: &BTreeSet<Variable>,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<ImplicationVerdict, ImplicationError>> {
    // One span per problem: the check and the grading's counterexample query.
    let _span = measure::algorithm_span(Algorithm::BackendImplicationCheck);
    check_established(
        definition,
        antecedent,
        antecedent_existentials,
        consequent,
        consequent_existentials,
        SimplificationOptions::default(),
        solver,
    )
    .and_then(|checked| grade_verdict(checked, definition, solver).map_err(Unwind::Stop))
    .layered()
}

/// Check whether an antecedent is covered by the union of several consequents, under the proof
/// policy.
///
/// A reachability destination is a disjunction, so proving each branch in
/// isolation is sufficient but not complete. This operation matches every
/// branch, combines the residual branch conditions with logical `or`, and
/// asks the solver to discharge that combined obligation.
pub fn check_disjunctive_implication_with_existentials(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    consequents: &[Pattern],
    consequent_existentials: &BTreeSet<Variable>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Coverage, ImplicationError>> {
    if let [consequent] = consequents {
        return check_implication_with_existentials_and_options(
            definition,
            antecedent,
            &BTreeSet::new(),
            consequent,
            consequent_existentials,
            options,
            solver,
        );
    }
    // One span per problem: the check and its grading.
    let _span = measure::algorithm_span(Algorithm::BackendImplicationCheck);
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "TermKind is syntax; only the listed variants are special here"
    )]
    let antecedent_variable = match antecedent.term.kind() {
        crate::term::TermKind::Variable(variable) => Some(variable.clone()),
        _ => None,
    };
    establish_disjunction(
        definition,
        antecedent,
        consequents,
        consequent_existentials,
        options,
        solver,
    )
    .and_then(|(established, antecedent)| {
        let established =
            empty_unless_consistent(definition, &antecedent, established, options, solver)?;
        Ok(grade_coverage(Checked {
            established,
            antecedent,
            antecedent_variable,
        }))
    })
    .layered()
}

/// The disjunctive check's policy-neutral part: what it established, and the antecedent it
/// established it on.
fn establish_disjunction(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    consequents: &[Pattern],
    consequent_existentials: &BTreeSet<Variable>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> CheckResult<(Established, Pattern)> {
    let mut antecedent = antecedent.clone();
    if predicates_truth(&antecedent.constraints) == Truth::False
        || matches!(
            solver.is_sat(&antecedent.constraints, &Substitution::new())?,
            Ok(Satisfiability::Unsat)
        )
    {
        return Ok((Established::AntecedentEmpty, antecedent));
    }
    // Every disjunct is matched in the definition's normal form under the antecedent's
    // constraints, as the single destination is. Each later round's antecedent keeps those
    // constraints, so a disjunct simplified under them denotes the same set on its instances too.
    let destinations = consequents
        .iter()
        .map(|consequent| {
            Ok(Destination::prepare(
                definition,
                &antecedent,
                consequent,
                consequent_existentials,
                options,
                solver,
            )??)
        })
        .collect::<CheckResult<Vec<_>>>()?;

    // Invariant: `antecedent` is the last round's result; the loop repeats only while it changes.
    loop {
        let mut branches = Vec::new();
        // One refutation per matched branch whose obligation simplified to `false`, and the
        // obligations they refute.
        let mut refuted_branches = Vec::new();
        let mut refuted_obligations = Vec::new();
        let mut matched = false;
        // What this round left open: a matched branch whose obligations could not be prepared,
        // or a combined obligation that was neither refuted nor shown to hold.
        let mut open = None;
        // The antecedent's instances satisfy these facts (I7); every branch is decided on them.
        let knowledge = pattern_knowledge(definition, &antecedent);
        for destination in &destinations {
            let (substitution, remainder) = match match_terms_in_definition(
                MatchMode::Implies,
                definition,
                &destination.pattern().term,
                &antecedent.term,
            ) {
                MatchResult::Failed(FailReason::Subsorting(error)) => {
                    return Err(ImplicationError::Subsorting(error).into());
                }
                MatchResult::Failed(_) => continue,
                MatchResult::Indeterminate {
                    substitution,
                    remainder,
                } => (substitution, remainder),
                MatchResult::Success(substitution) => (substitution, Vec::new()),
            };
            matched = true;
            let (_, obligations, _) = consequent_obligations(
                definition,
                destination,
                substitution,
                remainder,
                &knowledge,
            );
            // A stop propagates before either fallback below sees the result: an obligation that
            // could not be prepared leaves the round open, but a stop is no answer to leave open.
            let obligations = match eliminate_and_quantify_obligation_branches(
                definition,
                obligations,
                destination.existentials(),
                &knowledge,
                options,
                solver,
            )
            .layered()?
            {
                Ok(obligations) => obligations,
                Err(_) => {
                    open = Some(Established::Unprepared);
                    continue;
                }
            };
            let predicates = match simplify_predicates_with_solver(
                definition,
                &obligations.predicates,
                &knowledge,
                options,
                solver,
            )? {
                Ok(predicates) => predicates,
                Err(_) => {
                    open = Some(Established::Unprepared);
                    continue;
                }
            };
            let obligations = Obligations {
                predicates,
                witnesses: obligations.witnesses,
            };
            let truth = predicates_truth(&obligations.predicates);
            match truth {
                Truth::True => {
                    let bindings = Bindings {
                        substitution: Substitution::new(),
                        witnesses: obligations.witnesses,
                    };
                    return Ok((Established::Holds(bindings), antecedent));
                }
                Truth::False => {
                    if let Some(refuted) = ObligationRefuted::by_simplifier(truth) {
                        refuted_branches.push(refuted);
                        refuted_obligations.push(conjoin(obligations.predicates));
                    }
                }
                Truth::Unknown => branches.push(obligations),
            }
        }

        // The destination's obligation is the disjunction of the matched branches'. It is
        // refuted when every disjunct is: each branch refuted above, and the disjunction of the
        // branches left undecided, which is decided as one disjunct below.
        let mut by = Refuter::Simplifier;
        if !branches.is_empty() {
            let witnesses = if let [branch] = branches.as_slice() {
                branch.witnesses.clone()
            } else {
                Substitution::new()
            };
            let holds = |witnesses| {
                Established::Holds(Bindings {
                    substitution: Substitution::new(),
                    witnesses,
                })
            };
            let undecided = |obligations| Established::Undecided {
                origin: Origin::ConsequentCondition,
                bindings: Bindings::default(),
                obligations,
            };
            let combined = vec![Predicate::Or(
                branches
                    .into_iter()
                    .map(|branch| conjoin(branch.predicates))
                    .collect(),
            )];
            let combined = match simplify_predicates_with_solver(
                definition, &combined, &knowledge, options, solver,
            )? {
                Ok(simplified) => simplified,
                Err(_) => combined,
            };
            // The combined obligation is refuted, or it leaves the round open with what the check
            // established about it.
            let truth = predicates_truth(&combined);
            let combined_open = match truth {
                Truth::True => return Ok((holds(witnesses), antecedent)),
                Truth::False => match ObligationRefuted::by_simplifier(truth) {
                    Some(refuted) => {
                        refuted_branches.push(refuted);
                        refuted_obligations.push(conjoin(combined));
                        None
                    }
                    None => Some(undecided(combined)),
                },
                Truth::Unknown => {
                    let verdict =
                        solver.check_predicates(&knowledge, &Substitution::new(), &combined)?;
                    if !matches!(
                        &verdict,
                        Ok(Validity::Valid | Validity::InconsistentGroundTruth)
                    ) && refuted_by_simplification(
                        definition, &knowledge, &combined, options, solver,
                    )
                    .layered()?
                    .unwrap_or(false)
                    {
                        return Ok((holds(witnesses), antecedent));
                    }
                    match verdict {
                        Ok(validity) => match validity {
                            Validity::Valid => return Ok((holds(witnesses), antecedent)),
                            Validity::InconsistentGroundTruth => {
                                return Ok((Established::AntecedentEmpty, antecedent));
                            }
                            Validity::Refuted => match ObligationRefuted::by_solver(&validity) {
                                Some(refuted) => {
                                    refuted_branches.push(refuted);
                                    refuted_obligations.push(conjoin(combined));
                                    by = Refuter::Solver;
                                    None
                                }
                                None => Some(undecided(combined)),
                            },
                            // The combined obligation holds on part of the antecedent and fails
                            // on a non-empty part; unless a branch is already open, every
                            // consequent was decided this round, so it is the exact coverage
                            // condition of the destination.
                            Validity::Contingent => Some(Established::Contingent {
                                origin: Origin::ConsequentCondition,
                                bindings: Bindings::default(),
                                obligations: combined,
                            }),
                            Validity::Unknown(_) => Some(undecided(combined)),
                        },
                        Err(_) => Some(undecided(combined)),
                    }
                }
            };
            if let Some(combined_open) = combined_open {
                open.get_or_insert(combined_open);
            }
        }

        if let Some(open) = open {
            let simplified = simplify_with_solver(
                definition,
                &antecedent.term,
                &antecedent.constraints,
                options,
                solver,
            )??
            .into_parts();
            let simplified = Pattern {
                term: simplified.term,
                constraints: merge_predicates(
                    antecedent.constraints.clone(),
                    simplified.conditions.into_predicates(),
                ),
            };
            if simplified != antecedent {
                antecedent = simplified;
                continue;
            }
            // At the antecedent fixed point, a combined obligation that holds on part of the
            // antecedent and fails on a non-empty part splits it.
            return Ok((open, antecedent));
        }
        // Every round that reaches this point decided each matched branch: a matched branch
        // whose obligation is refuted neither alone nor in the disjunction leaves the round
        // open above. A refuted condition is reported only with its refutation, and a matched
        // destination without one only as undecided.
        let established = match ObligationRefuted::every_branch(refuted_branches) {
            Some(refuted) => Established::Refuted {
                refuted,
                by,
                origin: Origin::ConsequentCondition,
                bindings: Bindings::default(),
                obligations: vec![disjoin(refuted_obligations)],
            },
            // Not reached (see above); nothing is established about the matched destination.
            None if matched => Established::Unprepared,
            None => Established::TermMismatch,
        };
        return Ok((established, antecedent));
    }
}

/// Check an implication under the proof policy, with explicit simplification options.
pub fn check_implication_with_existentials_and_options(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    antecedent_existentials: &BTreeSet<Variable>,
    consequent: &Pattern,
    consequent_existentials: &BTreeSet<Variable>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Result<Coverage, ImplicationError>> {
    // One span per problem: the check and its grading.
    let _span = measure::algorithm_span(Algorithm::BackendImplicationCheck);
    check_established(
        definition,
        antecedent,
        antecedent_existentials,
        consequent,
        consequent_existentials,
        options,
        solver,
    )
    .map(grade_coverage)
    .layered()
}

/// The policy-neutral check: match the consequent against the antecedent, simplifying the
/// antecedent between rounds while the match stays indeterminate, and discharge the match's
/// obligations on the last round's antecedent.
fn check_established(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    antecedent_existentials: &BTreeSet<Variable>,
    consequent: &Pattern,
    consequent_existentials: &BTreeSet<Variable>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> CheckResult<Checked> {
    let destination = Destination::prepare(
        definition,
        antecedent,
        consequent,
        consequent_existentials,
        options,
        solver,
    )??;
    // A free variable of the consequent that is not existential is universal over the whole
    // implication, so an antecedent existential of the same name is a different variable.
    let mut antecedent =
        rename_existentials_apart(antecedent, antecedent_existentials, destination.pattern())
            .unwrap_or_else(|| antecedent.clone());
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "TermKind is syntax; only the listed variants are special here"
    )]
    let antecedent_variable = match antecedent.term.kind() {
        crate::term::TermKind::Variable(variable) => Some(variable.clone()),
        _ => None,
    };
    let established = if predicates_truth(&antecedent.constraints) == Truth::False
        || matches!(
            solver.is_sat(&antecedent.constraints, &Substitution::new())?,
            Ok(Satisfiability::Unsat)
        ) {
        Established::AntecedentEmpty
    } else {
        // Invariant: `antecedent` is the last round's result; the loop repeats only while it
        // changes.
        loop {
            match match_terms_in_definition(
                MatchMode::Implies,
                definition,
                &destination.pattern().term,
                &antecedent.term,
            ) {
                MatchResult::Failed(FailReason::Subsorting(error)) => {
                    return Err(ImplicationError::Subsorting(error).into());
                }
                MatchResult::Failed(_) => break Established::TermMismatch,
                MatchResult::Indeterminate {
                    substitution,
                    remainder,
                } => {
                    let simplified = simplify_with_solver(
                        definition,
                        &antecedent.term,
                        &antecedent.constraints,
                        options,
                        solver,
                    )??
                    .into_parts();
                    let simplified = Pattern {
                        term: simplified.term,
                        constraints: merge_predicates(
                            antecedent.constraints.clone(),
                            simplified.conditions.into_predicates(),
                        ),
                    };
                    if simplified == antecedent {
                        break discharge_consequent(
                            definition,
                            &antecedent,
                            &destination,
                            substitution,
                            remainder,
                            options,
                            solver,
                        )?;
                    }
                    antecedent = simplified;
                }
                MatchResult::Success(substitution) => {
                    break discharge_consequent(
                        definition,
                        &antecedent,
                        &destination,
                        substitution,
                        Vec::new(),
                        options,
                        solver,
                    )?;
                }
            }
        }
    };
    let established =
        empty_unless_consistent(definition, &antecedent, established, options, solver)?;
    Ok(Checked {
        established,
        antecedent,
        antecedent_variable,
    })
}

/// `established`, or `AntecedentEmpty` when it is a matched consequent the check did not show to
/// hold and the antecedent's knowledge is contradictory.
///
/// A match's obligations are simplified and decided on `pattern_knowledge(antecedent)` (I7): the
/// constraints with the definedness of their atoms stated, and the definedness `⌈t⌉` of the term.
/// Those facts can contradict each other where the constraints alone are satisfiable, which the
/// check's first emptiness test, on the constraints, does not see: `M Map (1 |-> 2) ∧ (1 in_keys
/// M)` has no instance, since the concatenation is defined only where `1` is not a key of `M`. On
/// contradictory knowledge the simplifier and the solver may refute any obligation, and every such
/// refutation, like every other statement about the instances, holds vacuously. The verdict that
/// is true there is that the antecedent has no instance, so before a refuted, undecided or
/// unprepared match is graded, the knowledge is decided (`knowledge_is_contradictory`).
///
/// `Holds` and `AntecedentEmpty` need no such decision, and `TermMismatch` decided no obligation:
/// it is kept as established, so a state whose term does not match the destination, which a proof
/// meets at every step before reaching it, costs no further simplification.
///
/// `Contingent` is kept too: the check has already searched a stronger set of facts for a
/// contradiction. The solver answered it for the obligations `o` on the knowledge as written, with
/// `knowledge ∧ o` and `knowledge ∧ ¬o` both satisfiable, and `refuted_by_simplification`
/// simplified `knowledge ∧ ¬o` as one conjunction and found it neither `false` nor `Unsat`. Every
/// fact of the knowledge is among those, so a contradiction between them is one of that
/// conjunction, which the same simplifier and solver did not find. Deciding the knowledge again
/// would repeat that search on fewer facts, at the cost of one more simplification of the whole
/// knowledge and one more solver query on every contingent step of a proof. What is lost is a
/// contradiction the simplifier exposes only without `¬o`, or one behind a failed simplification
/// of the conjunction: such a state stays `Contingent`, which, like every statement about an
/// empty state, holds.
fn empty_unless_consistent(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    established: Established,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<Established> {
    match &established {
        Established::Holds(_)
        | Established::AntecedentEmpty
        | Established::TermMismatch
        | Established::Contingent { .. } => Ok(established),
        Established::Refuted { .. } | Established::Undecided { .. } | Established::Unprepared => {
            let knowledge = pattern_knowledge(definition, antecedent);
            Ok(
                if knowledge_is_contradictory(definition, &knowledge, options, solver)? {
                    Established::AntecedentEmpty
                } else {
                    established
                },
            )
        }
    }
}

/// Whether the facts `knowledge`, which every instance of a pattern satisfies, are shown
/// contradictory, so that the pattern has no instance: they are syntactically false, they simplify
/// to `false`, or the solver answers `Unsat` for them. Simplification preserves their meaning, and
/// an `Unsat` answer refutes whatever the translation approximated. A failed simplification leaves
/// the facts as they are for the solver.
fn knowledge_is_contradictory(
    definition: &BackendDefinition,
    knowledge: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Stoppable<bool> {
    if predicates_truth(knowledge) == Truth::False {
        return Ok(true);
    }
    let simplified = simplify_predicates_with_solver(definition, knowledge, &[], options, solver)?;
    let facts = match &simplified {
        Ok(simplified) if predicates_truth(simplified) == Truth::False => return Ok(true),
        Ok(simplified) => simplified.as_slice(),
        Err(_) => knowledge,
    };
    Ok(matches!(
        solver.is_sat(facts, &Substitution::new())?,
        Ok(Satisfiability::Unsat)
    ))
}

/// The proof policy's grading: which instances of the state lie in the destination. It needs no
/// solver: a refuted part carries the refutation the check established.
fn grade_coverage(checked: Checked) -> Coverage {
    let Checked {
        established,
        antecedent: _,
        antecedent_variable,
    } = checked;
    match established {
        Established::Holds(bindings) => Coverage::Covered(bindings),
        Established::AntecedentEmpty => Coverage::Vacuous,
        Established::TermMismatch => Coverage::TermMismatch,
        // The covered part is the instances that satisfy every obligation: `covered` keeps an
        // equation `X = t` that binds the antecedent's variable among them, so for a state whose
        // term is `X` the uncovered part is the state under `¬(X = t)`, not the state under
        // `¬⊤ = ⊥`.
        Established::Refuted {
            refuted,
            by: _,
            origin: Origin::MatchRemainder,
            bindings,
            obligations,
        } => Coverage::PartialCoverage {
            coverage: CoverageCondition::partial(
                antecedent_variable.as_ref(),
                bindings,
                obligations,
            ),
            refuted,
        },
        Established::Refuted {
            refuted,
            by: _,
            origin: Origin::ConsequentCondition,
            bindings,
            obligations: _,
        } => Coverage::ConditionRefuted {
            report: MatchReport::refuted(bindings),
            refuted,
        },
        // The obligations hold on part of the state and fail on a non-empty part, so they are
        // the exact coverage condition, whatever their origin.
        Established::Contingent {
            origin: _,
            bindings,
            obligations,
        } => Coverage::Contingent(CoverageCondition::contingent(bindings, obligations)),
        Established::Undecided { .. } | Established::Unprepared => Coverage::Undecided,
    }
}

/// The complete policy's grading: does every instance of the antecedent lie in the consequent?
///
/// Every failing part is graded by [`grade_outside`], the one path to an `Invalid` verdict. `Err`
/// is a stop of its solver query.
fn grade_verdict(
    checked: Checked,
    definition: &BackendDefinition,
    solver: &dyn SmtSolver,
) -> Stoppable<ImplicationVerdict> {
    let Checked {
        established,
        antecedent,
        antecedent_variable,
    } = checked;
    // `empty_unless_consistent` decided the emptiness of a refuted, undecided or unprepared
    // match, and a contingent one was searched for a contradiction on stronger facts; a term
    // mismatch decided nothing, so its grading decides it.
    let grade = |outside, evidence, emptiness| {
        grade_outside(
            definition,
            &antecedent,
            outside,
            evidence,
            emptiness,
            solver,
        )
    };
    let refuted_everywhere = |refuted| OutsideEvidence::Everywhere(Everywhere::Refuted(refuted));
    match established {
        Established::Holds(bindings) => Ok(ImplicationVerdict::Valid(bindings)),
        Established::AntecedentEmpty => Ok(ImplicationVerdict::VacuouslyValid),
        Established::TermMismatch => grade(
            Outside::TermMismatch,
            OutsideEvidence::Everywhere(Everywhere::TermMismatch),
            Emptiness::Undecided,
        ),
        // A remainder obligation refuted by the simplifier is reported as a term mismatch, and
        // one refuted by the solver as partial coverage; either puts every instance outside.
        Established::Refuted {
            refuted,
            by: Refuter::Simplifier,
            origin: Origin::MatchRemainder,
            bindings: _,
            obligations: _,
        } => grade(
            Outside::TermMismatch,
            refuted_everywhere(refuted),
            Emptiness::Decided,
        ),
        Established::Refuted {
            refuted,
            by: Refuter::Solver,
            origin: Origin::MatchRemainder,
            bindings,
            obligations,
        } => grade(
            Outside::PartialCoverage(CoverageCondition::partial(
                antecedent_variable.as_ref(),
                bindings,
                obligations,
            )),
            refuted_everywhere(refuted),
            Emptiness::Decided,
        ),
        Established::Refuted {
            refuted,
            by: _,
            origin: Origin::ConsequentCondition,
            bindings,
            obligations: _,
        } => grade(
            Outside::ConsequentCondition(MatchReport::refuted(bindings)),
            refuted_everywhere(refuted),
            Emptiness::Decided,
        ),
        // The instances that falsify the obligations are outside; the report is the part of
        // the antecedent that would lie in the consequent, or the match's bindings.
        Established::Contingent {
            origin: Origin::MatchRemainder,
            bindings,
            obligations,
        } => {
            let coverage = CoverageCondition::partial(
                antecedent_variable.as_ref(),
                bindings,
                obligations.clone(),
            );
            grade(
                Outside::PartialCoverage(coverage),
                OutsideEvidence::Where(obligations),
                Emptiness::Decided,
            )
        }
        Established::Contingent {
            origin: Origin::ConsequentCondition,
            bindings,
            obligations,
        } => grade(
            Outside::ConsequentCondition(MatchReport::contingent(bindings)),
            OutsideEvidence::Where(obligations),
            Emptiness::Decided,
        ),
        // An undecided remainder obligation is reported as the condition under which the
        // implication would hold; nothing is shown outside.
        Established::Undecided {
            origin: Origin::MatchRemainder,
            bindings,
            obligations,
        } => Ok(ImplicationVerdict::Indeterminate {
            outside: Some(Outside::PartialCoverage(CoverageCondition::partial(
                antecedent_variable.as_ref(),
                bindings,
                obligations,
            ))),
        }),
        Established::Undecided {
            origin: Origin::ConsequentCondition,
            ..
        }
        | Established::Unprepared => Ok(ImplicationVerdict::Indeterminate { outside: None }),
    }
}

/// Whether the check already decided if the antecedent has no instance, before a failing part
/// of the consequent is graded ([`grade_outside`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Emptiness {
    /// The check decided it and did not show the antecedent empty: `empty_unless_consistent`
    /// decided the knowledge of a refuted match, and a contingent match was searched for a
    /// contradiction among facts that include the knowledge (`refuted_by_simplification`).
    Decided,
    /// Nothing decided it: the consequent's term did not match, so no obligation was decided on
    /// the antecedent's knowledge, or the consequent is `\bottom`, which has no match at all.
    Undecided,
}

/// Grade a failing part of the consequent under the complete policy.
///
/// `A -> C` holds when every instance of `A` lies in `C`, so it holds of an `A` with no instance
/// whatever `C` is, its term included. Each failing part names the instances of `A` outside `C`;
/// it says nothing about whether there are any.
///
/// `Invalid` asserts an instance of the antecedent outside the consequent, so it is answered
/// only when `Counterexample::outside` shows one from `evidence`: an instance of the antecedent
/// when every instance is outside, or an instance of the antecedent conjoined with the negated
/// obligations when those instances are. Without that instance the implication may hold
/// vacuously. When `emptiness` is still undecided, it is decided here (`antecedent_is_empty`):
/// an antecedent shown to have no instance answers `VacuouslyValid`. Otherwise the answer is
/// `Indeterminate`, never `Valid`, since an emptiness the simplifier and the solver did not show
/// is not known; the report is kept, because it describes the antecedent's instances whether or
/// not there are any. Both decisions are made only on this failing path, after the check, so a
/// consequent that holds costs nothing more. A stop of a solver query is no answer about that
/// instance or that emptiness, so it is returned rather than graded `Indeterminate`.
fn grade_outside(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    outside: Outside,
    evidence: OutsideEvidence,
    emptiness: Emptiness,
    solver: &dyn SmtSolver,
) -> Stoppable<ImplicationVerdict> {
    if let Some(counterexample) =
        Counterexample::outside(definition, antecedent, &evidence, solver)?
    {
        return Ok(ImplicationVerdict::Invalid {
            counterexample,
            outside: Some(outside),
        });
    }
    Ok(
        if emptiness == Emptiness::Undecided
            && antecedent_is_empty(
                definition,
                antecedent,
                SimplificationOptions::default(),
                solver,
            )?
        {
            ImplicationVerdict::VacuouslyValid
        } else {
            ImplicationVerdict::Indeterminate {
                outside: Some(outside),
            }
        },
    )
}

/// Simplify the destination with the definition's equations under the antecedent's constraints
/// before matching ([`Destination::prepare`]). The match compares both sides in the definition's
/// normal form: a destination term with an unevaluated function application would leave an
/// obligation the equations could have discharged. The implication asks only about instances of
/// the antecedent, where its constraints hold, so the equations applied under them hold there and
/// the simplified destination denotes the same set on those instances. A top equation result
/// erases its conjunction operand, so `2 #And n +Int n` with `n +Int n = \top` becomes `2`. A
/// term that already carries the evaluated mark is kept. A simplification failure keeps the
/// destination as written, which denotes the same set; the check then proceeds on that form.
///
/// Where a simplification inside the check fails, the check falls back to a weaker but sound
/// step: the unsimplified form, or an indeterminate verdict. That is a fit answer to a bound or
/// to an error of the input. A stop is neither: the cancelled request, the passed step deadline,
/// the failed solver prelude or the exhausted stack belongs to the step or operation that runs
/// the check, and says nothing about the implication. So every fallback of the check, here and
/// in its other steps, is written on the failure layer of a layered result, after `?` has
/// propagated the stop to the check's owner.
fn simplify_consequent(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    consequent: Pattern,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> CheckResult<Pattern> {
    if consequent.term.attributes().evaluated {
        return Ok(consequent);
    }
    match simplify_with_solver(
        definition,
        &consequent.term,
        &antecedent.constraints,
        options,
        solver,
    )? {
        Ok(simplified) => {
            let simplified = simplified.into_parts();
            Ok(Pattern {
                term: simplified.term,
                constraints: merge_predicates(
                    consequent.constraints,
                    simplified.conditions.into_predicates(),
                ),
            })
        }
        Err(_) => Ok(consequent),
    }
}

/// ```toml algorithm-site
/// id = "backend.fresh.variables"
/// role = "part"
/// sites = ["freshen_existentials"]
/// ```
fn freshen_existentials(
    antecedent: &Pattern,
    consequent: &Pattern,
    existentials: &BTreeSet<Variable>,
) -> (Pattern, BTreeSet<Variable>) {
    let mut names = free_variables(antecedent)
        .into_iter()
        .chain(free_variables(consequent))
        .map(|variable| variable.name)
        .collect::<BTreeSet<_>>();
    // A renamed existential can be printed in the condition next to the request's variables,
    // so it is spelled like none of them.
    let mut request = RequestNames::of(&[antecedent, consequent]);
    request.add_variables(existentials);
    let mut substitution = Substitution::new();
    let mut fresh = BTreeSet::new();
    for (counter, original) in existentials.iter().enumerate() {
        let mut suffix = counter as u64;
        let name = fresh_name_apart(
            &original.name,
            FreshMarker::Exists,
            &mut suffix,
            &mut names,
            &request,
        );
        let variable = original.with_name(name);
        substitution.insert(
            original.clone(),
            crate::term::Term::variable(variable.clone()),
        );
        fresh.insert(variable);
    }
    #[expect(
        clippy::disallowed_methods,
        reason = "a renaming to fresh variables; a variable denotes an element"
    )]
    (
        Pattern {
            term: substitute(&consequent.term, &substitution),
            constraints: substitute_predicates(&consequent.constraints, &substitution),
        },
        fresh,
    )
}

/// Rename the existentials of `pattern` whose names occur free in `other`, or `None` when none
/// does.
fn rename_existentials_apart(
    pattern: &Pattern,
    existentials: &BTreeSet<Variable>,
    other: &Pattern,
) -> Option<Pattern> {
    let other_names = free_variables(other)
        .into_iter()
        .map(|variable| variable.name)
        .collect::<BTreeSet<_>>();
    let clashing = existentials
        .iter()
        .filter(|variable| other_names.contains(&variable.name))
        .collect::<Vec<_>>();
    if clashing.is_empty() {
        return None;
    }
    let mut names = free_variables(pattern)
        .into_iter()
        .map(|variable| variable.name)
        .chain(other_names)
        .collect::<BTreeSet<_>>();
    let mut request = RequestNames::of(&[pattern, other]);
    request.add_variables(existentials);
    let mut counter = 0;
    let substitution = clashing
        .into_iter()
        .map(|original| {
            let name = fresh_name_apart(
                &original.name,
                FreshMarker::Exists,
                &mut counter,
                &mut names,
                &request,
            );
            (
                original.clone(),
                crate::term::Term::variable(original.with_name(name)),
            )
        })
        .collect::<Substitution>();
    #[expect(
        clippy::disallowed_methods,
        reason = "a renaming to fresh variables; a variable denotes an element"
    )]
    Some(Pattern {
        term: substitute(&pattern.term, &substitution),
        constraints: substitute_predicates(&pattern.constraints, &substitution),
    })
}

/// Discharge the obligations of a match of the consequent against the antecedent: the match's
/// remainder equations, the bindings of universal consequent variables, and the consequent's
/// constraints, with the consequent's existential witnesses eliminated.
fn discharge_consequent(
    definition: &BackendDefinition,
    antecedent: &Pattern,
    destination: &Destination,
    substitution: Substitution,
    remainder: Vec<(crate::term::Term, crate::term::Term)>,
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> CheckResult<Established> {
    // Every obligation is decided on the antecedent's instances, where its term is defined and its
    // constraints hold with their definedness stated (I7).
    let knowledge = pattern_knowledge(definition, antecedent);
    let (consequent_match, obligations, origin) =
        consequent_obligations(definition, destination, substitution, remainder, &knowledge);
    // A stop propagates before either fallback below sees the result: obligations that could
    // not be prepared establish nothing, but a stop is no answer to establish nothing from.
    let obligations = match eliminate_and_quantify_obligation_branches(
        definition,
        obligations,
        destination.existentials(),
        &knowledge,
        options,
        solver,
    )
    .layered()?
    {
        Ok(obligations) => obligations,
        Err(_) => return Ok(Established::Unprepared),
    };
    let bindings = Bindings {
        substitution: consequent_match.into_reported(),
        witnesses: obligations.witnesses,
    };
    if obligations.predicates.is_empty() {
        return Ok(Established::Holds(bindings));
    }

    let obligations = match simplify_predicates_with_solver(
        definition,
        &obligations.predicates,
        &knowledge,
        options,
        solver,
    )? {
        Ok(predicates) => predicates,
        Err(_) => return Ok(Established::Unprepared),
    };
    let truth = predicates_truth(&obligations);
    match truth {
        Truth::True => return Ok(Established::Holds(bindings)),
        // Obligations simplified to `false` fail on every instance of the antecedent.
        Truth::False => {
            if let Some(refuted) = ObligationRefuted::by_simplifier(truth) {
                return Ok(Established::Refuted {
                    refuted,
                    by: Refuter::Simplifier,
                    origin,
                    bindings,
                    obligations,
                });
            }
        }
        Truth::Unknown => {}
    }

    let verdict = solver.check_predicates(&knowledge, &Substitution::new(), &obligations)?;
    if !matches!(
        &verdict,
        Ok(Validity::Valid | Validity::InconsistentGroundTruth)
    ) && refuted_by_simplification(definition, &knowledge, &obligations, options, solver)
        .layered()?
        .unwrap_or(false)
    {
        return Ok(Established::Holds(bindings));
    }
    Ok(match verdict {
        Ok(validity) => match validity {
            Validity::Valid => Established::Holds(bindings),
            Validity::InconsistentGroundTruth => Established::AntecedentEmpty,
            Validity::Refuted => match ObligationRefuted::by_solver(&validity) {
                Some(refuted) => Established::Refuted {
                    refuted,
                    by: Refuter::Solver,
                    origin,
                    bindings,
                    obligations,
                },
                None => Established::Undecided {
                    origin,
                    bindings,
                    obligations,
                },
            },
            Validity::Contingent => Established::Contingent {
                origin,
                bindings,
                obligations,
            },
            Validity::Unknown(_) => Established::Undecided {
                origin,
                bindings,
                obligations,
            },
        },
        Err(_) => Established::Undecided {
            origin,
            bindings,
            obligations,
        },
    })
}

/// The obligation branches of `destination`'s match against an antecedent whose instances
/// `knowledge` describes, the match `substitution` and `remainder` given: the remainder's
/// collection pairs solved or merged (`solve_collection_remainder_pairs`), the rest expanded
/// into branches (`ConsequentMatch::obligation_branches`), and the constraints the solve states
/// added to each branch. The origin names what the obligations come from: the destination's
/// condition alone when no remainder is left, the match remainder otherwise. A single
/// destination and each disjunct of a disjunctive one are decided through this one prologue.
fn consequent_obligations(
    definition: &BackendDefinition,
    destination: &Destination,
    substitution: Substitution,
    remainder: Vec<(crate::term::Term, crate::term::Term)>,
    knowledge: &[Predicate],
) -> (ConsequentMatch, Vec<ConsequentObligations>, Origin) {
    let (substitution, remainder, solved_constraints) = solve_collection_remainder_pairs(
        definition,
        substitution,
        remainder,
        destination.existentials(),
        &destination.pattern().constraints,
    );
    let origin = if remainder.is_empty() {
        Origin::ConsequentCondition
    } else {
        Origin::MatchRemainder
    };
    let consequent_match = ConsequentMatch::new(substitution, destination.existentials());
    let mut obligations =
        consequent_match.obligation_branches(definition, destination, remainder, knowledge);
    for branch in &mut obligations {
        branch.add_solved(&solved_constraints, knowledge);
    }
    (consequent_match, obligations, origin)
}

/// Whether the antecedent's instances, described by `knowledge`, admit no counterexample to
/// `obligations` once the simplifier evaluates functions under the negated obligations. A
/// failure of the simplification is the caller's to fall back on; a stop is not.
fn refuted_by_simplification(
    definition: &BackendDefinition,
    knowledge: &[Predicate],
    obligations: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<bool, Unwind<SimplificationError>> {
    let counterexample =
        normalize_predicate(Predicate::Not(Box::new(conjoin(obligations.to_vec()))));
    let mut conjuncts = knowledge.to_vec();
    conjuncts.push(counterexample);
    let simplified =
        simplify_predicates_with_solver(definition, &conjuncts, &[], options, solver)??;
    Ok(predicates_truth(&simplified) == Truth::False
        || matches!(
            solver.is_sat(&simplified, &Substitution::new())?,
            Ok(Satisfiability::Unsat)
        ))
}

fn quantify_obligations(
    obligations: Vec<Predicate>,
    existentials: &BTreeSet<Variable>,
) -> Vec<Predicate> {
    if obligations.is_empty() {
        return obligations;
    }
    let free = obligations
        .iter()
        .flat_map(Predicate::free_variables)
        .collect::<BTreeSet<_>>();
    let quantified = existentials
        .iter()
        .filter(|variable| free.contains(*variable))
        .cloned()
        .collect::<Vec<_>>();
    if quantified.is_empty() {
        return obligations;
    }
    let mut obligation = conjoin(obligations);
    for variable in quantified.into_iter().rev() {
        obligation = Predicate::Exists(variable, Box::new(obligation));
    }
    vec![obligation]
}

fn eliminate_and_quantify_obligation_branches(
    definition: &BackendDefinition,
    branches: Vec<ConsequentObligations>,
    existentials: &BTreeSet<Variable>,
    known: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Obligations, Unwind<SimplificationError>> {
    let mut prepared = Vec::with_capacity(branches.len());
    for branch in branches {
        let mut obligations = eliminate_existential_witnesses(
            definition,
            branch.into_predicates(),
            existentials,
            known,
            options,
            solver,
        )?;
        let remaining = existentials
            .iter()
            .filter(|variable| !obligations.witnesses.contains_key(*variable))
            .cloned()
            .collect::<BTreeSet<_>>();
        obligations.predicates = quantify_obligations(obligations.predicates, &remaining);
        prepared.push(obligations);
    }
    Ok(combine_obligation_branches(prepared))
}

fn eliminate_existential_witnesses(
    definition: &BackendDefinition,
    branch: Vec<Predicate>,
    existentials: &BTreeSet<Variable>,
    known: &[Predicate],
    options: SimplificationOptions,
    solver: &dyn SmtSolver,
) -> Result<Obligations, Unwind<SimplificationError>> {
    let mut branch = simplify_predicates_with_solver(definition, &branch, known, options, solver)??;
    branch.retain(|predicate| !matches!(predicate, Predicate::True));
    let mut witnesses = Substitution::new();
    if predicates_truth(&branch) == Truth::False {
        return Ok(Obligations {
            predicates: vec![Predicate::False],
            witnesses,
        });
    }

    let mut remaining = existentials.clone();
    // A round that finds no witness exits; one that finds some removes them from `remaining`.
    // Invariant: `remaining` holds the existentials that have no witness yet.
    loop {
        let (found, rest) = extract_substitution_for(&branch, &remaining, definition.sort_graph());
        if found.is_empty() {
            break;
        }
        remaining.retain(|variable| !found.contains_key(variable));
        witnesses = compose(&found, &witnesses);
        // `∃e. (e = t ∧ ψ)` is `⌈t⌉ ∧ ψ[t/e]` for an element variable `e` (I2): the witness's
        // definedness stays an obligation unless the antecedent's knowledge holds it.
        branch = simplify_predicates_with_solver(
            definition,
            &eliminate_bindings(definition, &rest, &found, known),
            known,
            options,
            solver,
        )??;
        branch.retain(|predicate| !matches!(predicate, Predicate::True));
        if predicates_truth(&branch) == Truth::False {
            return Ok(Obligations {
                predicates: vec![Predicate::False],
                witnesses,
            });
        }
    }

    // The witnesses found above are already eliminated: an extracted substitution is saturated,
    // so `rest` under it mentions none of its variables. Only a residual match remains; its
    // equation holds under the match, and its witnesses' definedness is kept (I2).
    let mut residual = Substitution::new();
    if let Some(found) = residual_existential_equality_match(definition, &branch, &remaining) {
        witnesses = compose(&found, &witnesses);
        branch.clear();
        residual = found;
    }

    Ok(Obligations {
        predicates: eliminate_bindings(definition, &branch, &residual, known),
        witnesses,
    })
}

fn residual_existential_equality_match(
    definition: &BackendDefinition,
    branch: &[Predicate],
    remaining: &BTreeSet<Variable>,
) -> Option<Substitution> {
    let [Predicate::Equals(left, right)] = branch else {
        return None;
    };
    for (pattern, subject) in [(left, right), (right, left)] {
        if pattern.attributes().variables.is_disjoint(remaining) {
            continue;
        }
        if let MatchResult::Success(substitution) =
            match_terms_in_definition(MatchMode::Implies, definition, pattern, subject)
            && substitution
                .keys()
                .all(|variable| remaining.contains(variable))
        {
            return Some(substitution);
        }
    }
    None
}

fn combine_obligation_branches(mut branches: Vec<Obligations>) -> Obligations {
    match branches.len() {
        0 => Obligations {
            predicates: vec![Predicate::False],
            witnesses: Substitution::new(),
        },
        1 => branches.pop().expect("one implication branch is present"),
        _ => {
            if let Some(index) = branches
                .iter()
                .position(|branch| predicates_truth(&branch.predicates) == Truth::True)
            {
                return branches.swap_remove(index);
            }
            Obligations {
                predicates: vec![Predicate::Or(
                    branches
                        .into_iter()
                        .map(|branch| conjoin(branch.predicates))
                        .collect(),
                )],
                witnesses: Substitution::new(),
            }
        }
    }
}

/// Solve the collection pairs of a match remainder with the collection solver that rule
/// application uses (`solve_collection_pairs_in_definition`): opaque chunks common to both
/// sides cancel, since the parts of a defined concatenation are disjoint, and a destination
/// frame that is the sole remaining opaque term is bound to the subject's leftover, the one
/// value that makes the two sides equal.
/// Several such frames of one destination set or map are one frame (`merge_free_parts`) when
/// each is an existential that occurs nowhere else in what the check decides: not bound by the
/// match, not in another pair of the remainder, not in the subject, and not in the
/// `constraints` of the destination. Their union is then the only thing the destination states
/// of them, and any split of the leftover between them is a witness; the first takes it all and
/// the others are empty.
/// A solution is taken only when it is unique and binds destination existentials alone; any
/// other outcome leaves the pairs as equality obligations, with the merge kept: it is an
/// equivalence on its own (the merged pair, and the other merged parts bound to the empty
/// collection), so a later expansion of the pairs (`expand_implication_remainders`) sees one
/// part where the destination wrote several.
/// A subject that is an update of a map or a union with a set of items, against a destination
/// of that collection, is first written as the collection it equals
/// ([`subject_collection_form`]), so such a pair is a collection pair too.
fn solve_collection_remainder_pairs(
    definition: &BackendDefinition,
    substitution: Substitution,
    remainder: Vec<(crate::term::Term, crate::term::Term)>,
    existentials: &BTreeSet<Variable>,
    constraints: &[Predicate],
) -> (
    Substitution,
    Vec<(crate::term::Term, crate::term::Term)>,
    Vec<Predicate>,
) {
    let remainder = remainder
        .into_iter()
        .map(|(pattern, subject)| {
            let subject =
                subject_collection_form(definition, &pattern, &subject).unwrap_or(subject);
            (pattern, subject)
        })
        .collect::<Vec<_>>();
    let collections = remainder
        .iter()
        .filter(|(left, right)| is_collection_pair(left, right))
        .cloned()
        .collect::<Vec<_>>();
    if collections.is_empty() {
        return (substitution, remainder, Vec::new());
    }
    let constraint_variables = constraints
        .iter()
        .flat_map(Predicate::free_variables)
        .collect::<BTreeSet<_>>();
    let mut initial = substitution.clone();
    let mut pairs = Vec::with_capacity(collections.len());
    // The remainder with each collection pair replaced by its merged form, in its order.
    let mut merged_remainder = Vec::with_capacity(remainder.len());
    for (index, (pattern, subject)) in remainder.iter().enumerate() {
        if !is_collection_pair(pattern, subject) {
            merged_remainder.push((pattern.clone(), subject.clone()));
            continue;
        }
        let free = |variable: &Variable| {
            existentials.contains(variable)
                && !substitution.contains_key(variable)
                && !constraint_variables.contains(variable)
                && remainder.iter().enumerate().all(|(other, (left, right))| {
                    !right.attributes().variables.contains(variable)
                        && (other == index || !left.attributes().variables.contains(variable))
                })
        };
        match merge_free_parts(pattern, free) {
            Some((merged, empty)) => {
                initial.extend(empty);
                // Parts with no item merge into one variable, which is the subject.
                if let crate::term::TermKind::Variable(part) = merged.kind() {
                    initial.insert(part.clone(), subject.clone());
                } else {
                    pairs.push((merged.clone(), subject.clone()));
                    merged_remainder.push((merged, subject.clone()));
                }
            }
            None => {
                pairs.push((pattern.clone(), subject.clone()));
                merged_remainder.push((pattern.clone(), subject.clone()));
            }
        }
    }
    let solutions = solve_collection_pairs_in_definition(
        MatchMode::Implies,
        definition,
        initial.clone(),
        &pairs,
        None,
    );
    let Some([solution]) = solutions.as_deref() else {
        return (initial, merged_remainder, Vec::new());
    };
    let binds_only_existentials = solution
        .matched
        .substitution()
        .keys()
        .filter(|variable| !substitution.contains_key(*variable))
        .all(|variable| existentials.contains(variable));
    if !binds_only_existentials {
        return (initial, merged_remainder, Vec::new());
    }
    let remainder = remainder
        .into_iter()
        .filter(|pair| !collections.contains(pair))
        .collect();
    (
        solution.matched.substitution().clone(),
        remainder,
        solution.matched.conditions().to_vec(),
    )
}

fn is_collection_pair(left: &crate::term::Term, right: &crate::term::Term) -> bool {
    is_collection_term(left) && is_collection_term(right)
}

/// `subject` written as the collection term it equals, when `pattern` is a map or set
/// collection term and `subject` is, for that collection, a chain of `MAP.update` applications
/// or of `SET.union` applications with a set of items, and the definition declares the
/// collection's `MAP.remove` (`SET.difference`) function; `None` otherwise.
///
/// `M[K <- V]` binds `K` to `V` and every other key of `M` to its value in `M`, so it is the map
/// `K |-> V` beside `M` without `K`: that concatenation is defined, since `K` is no key of the
/// removal, and binds the same keys to the same values. Along a chain `M[K1 <- V1][K2 <- V2]`
/// the outer update wins for a key both write, so a key identical to one already taken is
/// skipped, and the chain is followed only while each new key is identical to every key taken
/// or certainly differs from each (two constructor-like keys that differ syntactically denote
/// different values), so the items taken have distinct keys and the removal of all of them
/// from the inner map is disjoint from them. Likewise `A |Set B`, with `B` a set of items (its
/// elements pairwise distinct, as an operand of the defined subject), is `B` beside `A -Set B`,
/// and so on along a chain of such unions whose items are identical or certainly differ.
///
/// The equation holds on every instance where the subject is defined (both functions are
/// total on defined operands), so a pair with the subject replaced states the same equality;
/// the subject is a subterm of the antecedent, defined on each of its instances.
fn subject_collection_form(
    definition: &BackendDefinition,
    pattern: &crate::term::Term,
    subject: &crate::term::Term,
) -> Option<crate::term::Term> {
    use crate::term::{CollectionMetadata, Term, TermKind};
    let collection = if let TermKind::Map { definition, .. } = pattern.kind() {
        CollectionMetadata::Map(definition.clone())
    } else if let TermKind::Set { definition, .. } = pattern.kind() {
        CollectionMetadata::Set(definition.clone())
    } else if let TermKind::Application { symbol, .. } = pattern.kind()
        && is_collection_term(pattern)
    {
        symbol.attributes.collection.clone()?
    } else {
        return None;
    };
    let hooked = |term: &Term, hook: &str| {
        let TermKind::Application {
            symbol, arguments, ..
        } = term.kind()
        else {
            return None;
        };
        (symbol.attributes.hook.as_deref() == Some(hook)
            && symbol.attributes.result_collection.as_ref() == Some(&collection))
        .then(|| (symbol.clone(), arguments.clone()))
    };
    // Each new item is identical to every item taken, or certainly differs from each.
    let fits = |taken: &[Term], item: &Term| {
        taken.iter().all(|other| {
            other == item
                || (other.attributes().constructor_like && item.attributes().constructor_like)
        })
    };
    let declared = |hook: &str, argument_sorts: &[crate::term::Sort]| {
        definition
            .symbols()
            .values()
            .find(|symbol| {
                symbol.attributes.hook.as_deref() == Some(hook)
                    && symbol.attributes.result_collection.as_ref() == Some(&collection)
                    && symbol.sort_variables.is_empty()
                    && symbol.argument_sorts == argument_sorts
            })
            .cloned()
    };
    match &collection {
        CollectionMetadata::Map(map) => {
            let (update, _) = hooked(subject, "MAP.update")?;
            let remove = declared("MAP.remove", update.argument_sorts.get(..2)?)?;
            let mut keys = Vec::new();
            let mut entries = Vec::new();
            let mut base = subject.clone();
            while let Some((_, arguments)) = hooked(&base, "MAP.update") {
                let [inner, key, value] = arguments.as_slice() else {
                    break;
                };
                if !fits(&keys, key) {
                    break;
                }
                if !keys.contains(key) {
                    keys.push(key.clone());
                    entries.push((key.clone(), value.clone()));
                }
                base = inner.clone();
            }
            if entries.is_empty() {
                return None;
            }
            let rest = keys.into_iter().fold(base, |rest, key| {
                Term::application(remove.clone(), Vec::new(), vec![rest, key])
            });
            Some(Term::map(map.clone(), entries, Some(rest)))
        }
        CollectionMetadata::Set(set) => {
            let (union, _) = hooked(subject, "SET.union")?;
            let difference = declared("SET.difference", &union.argument_sorts)?;
            let items = |term: &Term| {
                let TermKind::Set {
                    elements,
                    rest: None,
                    ..
                } = term.kind()
                else {
                    return None;
                };
                (!elements.is_empty()).then(|| elements.to_vec())
            };
            let mut elements: Vec<Term> = Vec::new();
            let mut base = subject.clone();
            while let Some((_, arguments)) = hooked(&base, "SET.union") {
                let [left, right] = arguments.as_slice() else {
                    break;
                };
                let Some((inner, added)) = items(right)
                    .map(|added| (left, added))
                    .or_else(|| items(left).map(|added| (right, added)))
                else {
                    break;
                };
                // The items of one operand are distinct already.
                if !added.iter().all(|element| fits(&elements, element)) {
                    break;
                }
                for element in added {
                    if !elements.contains(&element) {
                        elements.push(element);
                    }
                }
                base = inner.clone();
            }
            if elements.is_empty() {
                return None;
            }
            let removed = Term::set(set.clone(), elements.clone(), None);
            let rest = Term::application(difference, Vec::new(), vec![base, removed]);
            Some(Term::set(set.clone(), elements, Some(rest)))
        }
        CollectionMetadata::List(_) => None,
    }
}

fn remainder_obligation(left: &crate::term::Term, right: &crate::term::Term) -> Predicate {
    let Some(IteSplit {
        condition,
        then_pair,
        else_pair,
        ..
    }) = split_ite_pair(left, right)
    else {
        return Predicate::Equals(left.clone(), right.clone());
    };
    let then_obligation = remainder_obligation(&then_pair.0, &then_pair.1);
    let else_obligation = remainder_obligation(&else_pair.0, &else_pair.1);
    normalize_predicate(Predicate::Or(vec![
        normalize_predicate(Predicate::And(vec![
            Predicate::Term(condition.clone()),
            then_obligation,
        ])),
        normalize_predicate(Predicate::And(vec![
            Predicate::Not(Box::new(Predicate::Term(condition))),
            else_obligation,
        ])),
    ]))
}

fn free_variables(pattern: &Pattern) -> BTreeSet<Variable> {
    pattern
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            pattern
                .constraints
                .iter()
                .flat_map(Predicate::free_variables),
        )
        .collect()
}

fn merge_predicates(mut left: Vec<Predicate>, right: Vec<Predicate>) -> Vec<Predicate> {
    for predicate in right {
        if !left.contains(&predicate) {
            left.push(predicate);
        }
    }
    left
}

fn conjoin(mut predicates: Vec<Predicate>) -> Predicate {
    match predicates.len() {
        0 => Predicate::True,
        1 => predicates.pop().expect("one predicate is present"),
        _ => Predicate::And(predicates),
    }
}

fn disjoin(mut predicates: Vec<Predicate>) -> Predicate {
    match predicates.len() {
        0 => Predicate::False,
        1 => predicates.pop().expect("one predicate is present"),
        _ => Predicate::Or(predicates),
    }
}

fn implication_binding<'a>(
    variable: &'a crate::term::Term,
    value: &'a crate::term::Term,
    antecedent_variable: Option<&Variable>,
) -> Option<(&'a Variable, &'a crate::term::Term)> {
    let crate::term::TermKind::Variable(variable) = variable.kind() else {
        return None;
    };
    (antecedent_variable == Some(variable) && !value.attributes().variables.contains(variable))
        .then_some((variable, value))
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    use super::*;
    #[cfg(feature = "z3")]
    use crate::smt::Z3Solver;
    use crate::{
        definition::BackendDefinition,
        smt::{NoSolver, SmtError},
        stop::Stop,
        term::{Sort, Term},
    };

    // The checks on their failure layer, shadowing the entry points for the tests that arm no
    // stop: a stop is a test failure, reported with its cause. The test that expects a stop calls
    // the entry point itself (`super::`).

    fn unstopped<T>(result: Stoppable<Result<T, ImplicationError>>) -> Result<T, ImplicationError> {
        result.unwrap_or_else(|stop| {
            panic!(
                "the check stopped although no stop was armed: {}",
                stop.into_cause()
            )
        })
    }

    fn check_implication(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        consequent: &Pattern,
        solver: &dyn SmtSolver,
    ) -> Result<Coverage, ImplicationError> {
        unstopped(super::check_implication(
            definition, antecedent, consequent, solver,
        ))
    }

    fn check_implication_with_existentials(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        antecedent_existentials: &BTreeSet<Variable>,
        consequent: &Pattern,
        consequent_existentials: &BTreeSet<Variable>,
        solver: &dyn SmtSolver,
    ) -> Result<Coverage, ImplicationError> {
        unstopped(super::check_implication_with_existentials(
            definition,
            antecedent,
            antecedent_existentials,
            consequent,
            consequent_existentials,
            solver,
        ))
    }

    fn check_implication_with_existentials_complete(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        antecedent_existentials: &BTreeSet<Variable>,
        consequent: &Pattern,
        consequent_existentials: &BTreeSet<Variable>,
        solver: &dyn SmtSolver,
    ) -> Result<ImplicationVerdict, ImplicationError> {
        unstopped(super::check_implication_with_existentials_complete(
            definition,
            antecedent,
            antecedent_existentials,
            consequent,
            consequent_existentials,
            solver,
        ))
    }

    fn check_disjunctive_implication_with_existentials(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        consequents: &[Pattern],
        consequent_existentials: &BTreeSet<Variable>,
        options: SimplificationOptions,
        solver: &dyn SmtSolver,
    ) -> Result<Coverage, ImplicationError> {
        unstopped(super::check_disjunctive_implication_with_existentials(
            definition,
            antecedent,
            consequents,
            consequent_existentials,
            options,
            solver,
        ))
    }

    fn definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortTree{} []
                sort SortKItem{} []
                symbol pair{}(SortInt{}, SortInt{}) : SortKItem{} [constructor{}()]
                symbol succ{}(SortTree{}) : SortTree{} [constructor{}()]
                symbol f{}(SortInt{}) : SortInt{} [function{}()]
                symbol opaque{}(SortInt{}) : SortInt{} [function{}()]
                symbol sub{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), smt-hook{}("-")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(X:SortInt{}, \top{SortInt{}}())
                    )
                ) [label{}("identity-f"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    fn conditional_ite_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-symbol notBool{}(SortBool{}) : SortBool{}
                    [function{}(), total{}(), hook{}("BOOL.not")]
                hooked-symbol ite{}(SortBool{}, SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("KEQUAL.ite")]
                symbol f{}(SortBool{}) : SortInt{} [function{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortBool{}, R}(
                            B:SortBool{},
                            \dv{SortBool{}}("true")
                        ),
                        \and{R}(
                            \in{SortBool{}, R}(X0:SortBool{}, B:SortBool{}),
                            \top{R}()
                        )
                    ),
                    \equals{SortInt{}, R}(
                        f{}(X0:SortBool{}),
                        \and{SortInt{}}(
                            \dv{SortInt{}}("1"),
                            \top{SortInt{}}()
                        )
                    )
                ) [label{}("f-true")]
                axiom{R} \implies{R}(
                    \and{R}(
                        \equals{SortBool{}, R}(
                            notBool{}(B:SortBool{}),
                            \dv{SortBool{}}("true")
                        ),
                        \and{R}(
                            \in{SortBool{}, R}(X0:SortBool{}, B:SortBool{}),
                            \top{R}()
                        )
                    ),
                    \equals{SortInt{}, R}(
                        f{}(X0:SortBool{}),
                        \and{SortInt{}}(
                            \dv{SortInt{}}("0"),
                            \top{SortInt{}}()
                        )
                    )
                ) [label{}("f-false")]
            endmodule []"#,
        )
        .expect("conditional ITE definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("conditional ITE definition should internalize")
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(source).expect("term should parse"), &[])
            .expect("term should internalize")
    }

    fn pattern(definition: &BackendDefinition, source: &str) -> Pattern {
        Pattern {
            term: term(definition, source),
            constraints: Vec::new(),
        }
    }

    fn int(definition: &BackendDefinition, value: &str) -> Term {
        term(definition, &format!(r#"\dv{{SortInt{{}}}}("{value}")"#))
    }

    fn assert_single_witness(result: &Coverage, original_name: &str, expected: &Term) {
        let Coverage::Covered(bindings) = result else {
            panic!("a valid implication carries its bindings: {result:#?}");
        };
        assert_eq!(bindings.witnesses.len(), 1, "{bindings:#?}");
        let (variable, value) = bindings
            .witnesses
            .iter()
            .next()
            .expect("one witness was just required");
        assert!(
            variable.name.starts_with(original_name),
            "the refreshed witness should retain its source name: {variable:?}"
        );
        assert_eq!(value, expected);
    }

    #[derive(Clone, Debug)]
    struct FixedSolver {
        satisfiability: Result<Satisfiability, SmtError>,
        validity: Result<Validity, SmtError>,
    }

    impl SmtSolver for FixedSolver {
        fn is_sat(
            &self,
            _predicates: &[Predicate],
            _substitution: &Substitution,
        ) -> Stoppable<Result<Satisfiability, SmtError>> {
            Ok(self.satisfiability.clone())
        }

        fn check_predicates(
            &self,
            _known: &[Predicate],
            _substitution: &Substitution,
            _checked: &[Predicate],
        ) -> Stoppable<Result<Validity, SmtError>> {
            Ok(self.validity.clone())
        }
    }

    fn check_complete(
        definition: &BackendDefinition,
        antecedent: &Pattern,
        consequent: &Pattern,
        solver: &dyn SmtSolver,
    ) -> Result<ImplicationVerdict, ImplicationError> {
        check_implication_with_existentials_complete(
            definition,
            antecedent,
            &BTreeSet::new(),
            consequent,
            &BTreeSet::new(),
            solver,
        )
    }

    /// Whether the proof policy places every instance of the state in the destination: all of
    /// them are covered, or there is none.
    fn covers_every_instance(coverage: &Coverage) -> bool {
        matches!(coverage, Coverage::Covered(_) | Coverage::Vacuous)
    }

    /// The proof policy classifies a remainder obligation by the solver's answer alone, as it
    /// does an obligation without a remainder: a refuted one is partial coverage, a contingent
    /// one is the exact coverage condition, and an undecided one is indeterminate. The complete
    /// policy keeps reporting every undecided remainder obligation as its condition, and answers
    /// invalid only where an instance outside the consequent is shown.
    #[test]
    fn a_match_remainder_does_not_change_the_proof_policy_classification() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        let consequent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("1"))"#,
        );
        let obligation = Predicate::Equals(
            term(&definition, r#"\dv{SortInt{}}("0")"#),
            term(&definition, "X:SortInt{}"),
        );
        let solver = |validity| FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity,
        };

        let refuted = solver(Ok(Validity::Refuted));
        let result = check_implication(&definition, &antecedent, &consequent, &refuted)
            .expect("implication should be checked");
        assert!(
            matches!(result, Coverage::PartialCoverage { .. }),
            "{result:#?}"
        );
        let result = check_complete(&definition, &antecedent, &consequent, &refuted)
            .expect("implication should be checked");
        assert_eq!(result.status(), ImplicationStatus::Invalid, "{result:#?}");
        assert_eq!(
            result.failure(),
            Some(ImplicationFailure::PartialCoverage),
            "{result:#?}"
        );

        let contingent = solver(Ok(Validity::Contingent));
        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &contingent),
            Ok(Coverage::Contingent(CoverageCondition::contingent(
                Bindings::default(),
                vec![obligation],
            )))
        );

        for undecided in [
            solver(Ok(Validity::Unknown("timeout".into()))),
            solver(Err(SmtError::Unavailable)),
        ] {
            assert_eq!(
                check_implication(&definition, &antecedent, &consequent, &undecided),
                Ok(Coverage::Undecided)
            );
        }

        // The contingent answer's counterexample `X =/= 0` translates exactly and the solver
        // reports it satisfiable, so it is an instance outside the consequent; an undecided
        // answer shows none.
        for (undecided, status) in [
            (solver(Ok(Validity::Contingent)), ImplicationStatus::Invalid),
            (
                solver(Ok(Validity::Unknown("timeout".into()))),
                ImplicationStatus::Indeterminate,
            ),
            (
                solver(Err(SmtError::Unavailable)),
                ImplicationStatus::Indeterminate,
            ),
        ] {
            let result = check_complete(&definition, &antecedent, &consequent, &undecided)
                .expect("implication should be checked");
            assert_eq!(result.status(), status, "{result:#?}");
            assert_eq!(
                result.failure(),
                Some(ImplicationFailure::PartialCoverage),
                "{result:#?}"
            );
        }
    }

    #[test]
    fn identical_patterns_imply_each_other() {
        let definition = definition();
        let pattern = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);

        assert_eq!(
            check_implication(&definition, &pattern, &pattern, &NoSolver),
            Ok(Coverage::Covered(Bindings::default()))
        );
    }

    #[test]
    fn a_universal_binding_entailed_by_the_antecedent_is_valid() {
        let definition = definition();
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let antecedent = Pattern {
            term: term(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#),
            constraints: vec![Predicate::Equals(
                Term::variable(x.clone()),
                int(&definition, "1"),
            )],
        };
        let consequent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Ok(Coverage::Covered(Bindings {
                substitution: Substitution::from([(x, int(&definition, "1"))]),
                witnesses: Substitution::new(),
            }))
        );
    }

    /// `pair(X, 1) ∧ X = 2 ⇒ pair(X, X)` fails for the only value the antecedent allows: the match
    /// binding `X := 1` of the universal `X` is an equation the antecedent must entail.
    #[test]
    fn a_universal_binding_refuted_by_the_antecedent_is_invalid() {
        let definition = definition();
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let antecedent = Pattern {
            term: term(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#),
            constraints: vec![Predicate::Equals(
                Term::variable(x.clone()),
                int(&definition, "2"),
            )],
        };
        let consequent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);

        let result = check_implication(&definition, &antecedent, &consequent, &NoSolver)
            .expect("implication should be checked");

        let Coverage::ConditionRefuted { report, .. } = result else {
            panic!("the consequent condition is refuted: {result:#?}");
        };
        let condition = report.condition();
        assert_eq!(
            condition.substitution.get(&x),
            Some(&int(&definition, "1")),
            "{condition:#?}"
        );
    }

    /// `pair(Y, 1) ⇒ pair(X, 1)` with `X` free in the antecedent's condition binds the universal
    /// `X` to the antecedent variable `Y`, which holds only where the antecedent states `X = Y`.
    #[cfg(feature = "z3")]
    #[test]
    fn a_universal_bound_to_another_antecedent_variable_needs_their_equality() {
        let definition = definition();
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let consequent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        let antecedent = |condition: Predicate| Pattern {
            term: term(&definition, r#"pair{}(Y:SortInt{}, \dv{SortInt{}}("1"))"#),
            constraints: vec![condition],
        };
        let unrelated = antecedent(Predicate::Equals(
            Term::variable(x.clone()),
            Term::variable(x.clone()),
        ));
        let equal = antecedent(Predicate::Equals(
            Term::variable(x.clone()),
            Term::variable(y.clone()),
        ));

        // `X = Y` is satisfiable and so is its negation: the obligation holds on part of the
        // antecedent. The default check reports that part by its exact coverage condition, the
        // obligation itself; the complete check refutes with it.
        let result = check_implication(&definition, &unrelated, &consequent, &solver)
            .expect("implication should be checked");
        let Coverage::Contingent(coverage) = result else {
            panic!("the obligation holds on part of the antecedent: {result:#?}");
        };
        let condition = coverage.to_condition();
        assert_eq!(
            condition.predicates,
            vec![Predicate::Equals(
                Term::variable(x.clone()),
                Term::variable(y.clone())
            )],
            "{condition:#?}"
        );
        let result = check_implication_with_existentials_complete(
            &definition,
            &unrelated,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::new(),
            &solver,
        )
        .expect("implication should be checked");
        assert_eq!(result.status(), ImplicationStatus::Invalid, "{result:#?}");

        let result = check_implication(&definition, &equal, &consequent, &solver)
            .expect("implication should be checked");
        assert!(covers_every_instance(&result), "{result:#?}");
    }

    #[test]
    fn retains_a_simplifiable_occurs_check_as_a_partial_implication_condition() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"opaque{}(X:SortInt{})"#);
        let consequent = pattern(&definition, r#"X:SortInt{}"#);

        // The proof policy does not turn an undecided remainder obligation into a coverage
        // condition; the complete policy reports it as the condition of its answer, which stays
        // undecided because nothing shows an instance outside the consequent.
        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Ok(Coverage::Undecided)
        );
        let result = check_complete(&definition, &antecedent, &consequent, &NoSolver)
            .expect("implication should be checked");

        assert_eq!(result.status(), ImplicationStatus::Indeterminate);
        assert_eq!(result.failure(), Some(ImplicationFailure::PartialCoverage));
        let condition = result
            .into_condition()
            .expect("the recursively matched subset should be retained");
        assert!(matches!(
            condition.predicates.as_slice(),
            [Predicate::Equals(left, right)]
                if left == &term(&definition, "X:SortInt{}")
                    && right == &term(&definition, "opaque{}(X:SortInt{})")
        ));
    }

    #[test]
    fn promotes_a_partial_configuration_binding_into_the_implication_substitution() {
        let definition = definition();
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let antecedent = pattern(&definition, "X:SortInt{}");
        let value = int(&definition, "0");
        let consequent = Pattern {
            term: value.clone(),
            constraints: Vec::new(),
        };

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Ok(Coverage::Undecided)
        );
        let result = check_complete(&definition, &antecedent, &consequent, &NoSolver)
            .expect("implication should be checked");

        // Without a solver, no instance of `X` outside `0` is shown.
        assert_eq!(result.status(), ImplicationStatus::Indeterminate);
        let condition = result
            .into_condition()
            .expect("the partial configuration binding should be retained");
        assert_eq!(condition.substitution, Substitution::from([(x, value)]));
        assert!(condition.predicates.is_empty());
    }

    #[test]
    fn a_refuted_remainder_is_term_mismatch_only_under_the_complete_policy() {
        let definition = definition();
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let value = int(&definition, "0");
        let antecedent = Pattern {
            term: Term::variable(x.clone()),
            constraints: vec![Predicate::Not(Box::new(Predicate::Equals(
                Term::variable(x),
                value.clone(),
            )))],
        };
        let consequent = Pattern {
            term: value,
            constraints: vec![Predicate::False],
        };

        let result = check_implication_with_existentials_complete(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::new(),
            &NoSolver,
        )
        .expect("implication should be checked");

        // Every instance of the antecedent is refuted, but without a solver `X =/= 0` is not
        // shown to have one, so the refutation stays undecided.
        assert_eq!(
            result,
            ImplicationVerdict::Indeterminate {
                outside: Some(Outside::TermMismatch)
            }
        );
        assert_eq!(result.status(), ImplicationStatus::Indeterminate);
        assert_eq!(result.failure(), Some(ImplicationFailure::TermMismatch));
        assert_eq!(result.into_condition(), None);

        // The proof policy grades the simplifier-refuted remainder `0 = X` as uncovered coverage,
        // like a solver-refuted one, so the stuck check applies to it.
        let result = check_implication(&definition, &antecedent, &consequent, &NoSolver)
            .expect("implication should be checked");

        let Coverage::PartialCoverage { coverage, .. } = result else {
            panic!("the remainder obligation is refuted: {result:#?}");
        };
        assert!(
            coverage
                .to_condition()
                .predicates
                .contains(&Predicate::False),
            "{coverage:?}"
        );
        assert_eq!(coverage.covered(), Predicate::False, "{coverage:?}");
    }

    #[test]
    fn ite_obligations_split_on_a_symbolic_condition() {
        let definition = conditional_ite_definition();
        let outer_condition = term(&definition, "B:SortBool{}");
        let inner_condition = term(&definition, "C:SortBool{}");
        let subject = term(&definition, "X:SortInt{}");
        let then_branch = term(&definition, "Y:SortInt{}");
        let else_branch = term(&definition, "Z:SortInt{}");
        let inner_else_branch = term(&definition, "W:SortInt{}");
        let consequent = pattern(&definition, "X:SortInt{}");
        let destination = unstopped(Destination::prepare(
            &definition,
            &consequent,
            &consequent,
            &BTreeSet::new(),
            SimplificationOptions::default(),
            &NoSolver,
        ))
        .expect("the destination should be prepared");

        let branches = ConsequentMatch::new(Substitution::new(), destination.existentials())
            .obligation_branches(
                &definition,
                &destination,
                vec![(
                    subject.clone(),
                    term(
                        &definition,
                        concat!(
                            "ite{}(B:SortBool{}, ",
                            "ite{}(C:SortBool{}, Y:SortInt{}, W:SortInt{}), ",
                            "Z:SortInt{})",
                        ),
                    ),
                )],
                &[],
            );
        let [obligations] = <[_; 1]>::try_from(branches)
            .unwrap_or_else(|branches| panic!("one branch, found {}", branches.len()));

        assert_eq!(
            obligations.into_predicates(),
            [Predicate::Or(vec![
                Predicate::And(vec![
                    Predicate::Term(outer_condition.clone()),
                    Predicate::Or(vec![
                        Predicate::And(vec![
                            Predicate::Term(inner_condition.clone()),
                            Predicate::Equals(subject.clone(), then_branch),
                        ]),
                        Predicate::And(vec![
                            Predicate::Not(Box::new(Predicate::Term(inner_condition))),
                            Predicate::Equals(subject.clone(), inner_else_branch),
                        ]),
                    ]),
                ]),
                Predicate::And(vec![
                    Predicate::Not(Box::new(Predicate::Term(outer_condition))),
                    Predicate::Equals(subject, else_branch),
                ]),
            ])]
        );
    }

    #[test]
    fn refutation_by_simplification_evaluates_functions_under_the_negated_obligation() {
        let definition = conditional_ite_definition();
        let zero = int(&definition, "0");
        let antecedent = Pattern {
            term: int(&definition, "2"),
            constraints: vec![Predicate::Not(Box::new(Predicate::Equals(
                term(&definition, "f{}(B:SortBool{})"),
                zero,
            )))],
        };
        let consequent = pattern(
            &definition,
            "ite{}(B:SortBool{}, \\dv{SortInt{}}(\"2\"), \\dv{SortInt{}}(\"1\"))",
        );

        let result = check_implication(&definition, &antecedent, &consequent, &NoSolver)
            .expect("implication should be checked");

        // A covered state's condition is its bindings alone: the refuted counterexample leaves
        // no residual condition.
        assert!(
            matches!(result, Coverage::Covered(_)),
            "the refuted counterexample must leave no residual condition: {result:#?}"
        );
    }

    #[test]
    fn rejects_an_occurs_check_below_only_constructors() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"succ{}(X:SortTree{})"#);
        let consequent = pattern(&definition, r#"X:SortTree{}"#);

        let result = check_implication(&definition, &antecedent, &consequent, &NoSolver)
            .expect("implication should be checked");

        assert_eq!(result, Coverage::TermMismatch);
    }

    /// A free variable that only the consequent mentions is universal over the implication: its
    /// match binding is an obligation the antecedent must entail, like that of any universal.
    #[cfg(feature = "z3")]
    #[test]
    fn decides_free_variables_introduced_by_the_consequent() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        let check = |antecedent: &Pattern, consequent: &Pattern| {
            check_implication_with_existentials_complete(
                &definition,
                antecedent,
                &BTreeSet::new(),
                consequent,
                &BTreeSet::new(),
                &solver,
            )
            .expect("implication should be checked")
        };
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);

        // Constrained by the match: `Y := 1` does not hold for every `Y`.
        let constrained = pattern(&definition, r#"pair{}(X:SortInt{}, Y:SortInt{})"#);
        let result = check(&antecedent, &constrained);
        assert_eq!(result.status(), ImplicationStatus::Invalid, "{result:#?}");

        // A vacuous antecedent implies anything.
        let mut vacuous = antecedent.clone();
        vacuous.constraints = vec![
            Predicate::Equals(Term::variable(x.clone()), int(&definition, "0")),
            Predicate::Equals(Term::variable(x.clone()), int(&definition, "1")),
        ];
        let result = check(&vacuous, &constrained);
        assert_eq!(result.status(), ImplicationStatus::Valid, "{result:#?}");

        // Not constrained: `Y = 1 \/ Y =/= 1` holds for every `Y`.
        let mut unconstrained = antecedent.clone();
        unconstrained.constraints.clear();
        let mut consequent = antecedent.clone();
        let y_is_one = Predicate::Equals(Term::variable(y), int(&definition, "1"));
        consequent.constraints = vec![Predicate::Or(vec![
            y_is_one.clone(),
            Predicate::Not(Box::new(y_is_one)),
        ])];
        let result = check(&unconstrained, &consequent);
        assert_eq!(result.status(), ImplicationStatus::Valid, "{result:#?}");
    }

    /// An antecedent existential and a consequent universal of the same name are different
    /// variables: `(\exists X. pair(X, 1)) -> pair(X, 1)` fails whenever the two differ.
    #[cfg(feature = "z3")]
    #[test]
    fn antecedent_existentials_do_not_capture_consequent_universals() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let pair = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);

        let result = check_implication_with_existentials_complete(
            &definition,
            &pair,
            &BTreeSet::from([x]),
            &pair,
            &BTreeSet::new(),
            &solver,
        )
        .expect("implication should be checked");
        assert_eq!(result.status(), ImplicationStatus::Invalid, "{result:#?}");
    }

    #[test]
    fn consequent_existentials_are_not_treated_as_free_variables() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);
        let consequent = pattern(&definition, r#"pair{}(X:SortInt{}, Y:SortInt{})"#);
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &NoSolver,
        )
        .expect("implication should be checked");
        let Coverage::Covered(bindings) = result else {
            panic!("a valid result has bindings: {result:#?}");
        };
        assert!(bindings.witnesses.is_empty());
        assert_eq!(
            bindings.substitution.values().collect::<Vec<_>>(),
            vec![&Term::variable(crate::term::Variable::new(
                "X",
                Sort::simple("SortInt"),
            ))]
        );
    }

    fn set_frame_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortSet{}
                    [hook{}("SET.Set"), unit{}(setUnit{}()), element{}(setItem{}()), concat{}(setConcat{}())]
                sort SortS{} []
                sort SortCfg{} []
                hooked-symbol setUnit{}() : SortSet{}
                    [function{}(), total{}(), hook{}("SET.unit")]
                hooked-symbol setItem{}(SortInt{}) : SortSet{}
                    [function{}(), total{}(), hook{}("SET.element")]
                hooked-symbol setConcat{}(SortSet{}, SortSet{}) : SortSet{}
                    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]
                hooked-symbol setIn{}(SortInt{}, SortSet{}) : SortBool{}
                    [function{}(), total{}(), hook{}("SET.in")]
                symbol end{}() : SortS{} [constructor{}()]
                symbol cfg{}(SortS{}, SortSet{}) : SortCfg{} [constructor{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// Reduced from regression-new set_unification: the state `SetItem(I) (G2 F)` reached
    /// through a trusted claim must imply the destination `?G F`. Both sides contain the opaque
    /// frame F, which cancels because the parts of a defined set concatenation are disjoint,
    /// and the equation left binds the sole remaining opaque variable ?G to the leftover
    /// `SetItem(I) G2`; the existential frame is a witness found by collection solving, not by
    /// an equality conjunct.
    #[test]
    fn solves_an_existential_set_frame_against_the_shared_subject_frame() {
        let definition = set_frame_definition();
        let g = crate::term::Variable::new("G", Sort::simple("SortSet"));
        let consequent = pattern(
            &definition,
            "cfg{}(end{}(), setConcat{}(G:SortSet{}, F:SortSet{}))",
        );
        let antecedent = pattern(
            &definition,
            "cfg{}(end{}(), setConcat{}(setItem{}(I:SortInt{}), setConcat{}(G2:SortSet{}, F:SortSet{})))",
        );

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([g.clone()]),
            &NoSolver,
        )
        .expect("implication should be checked");

        let Coverage::Covered(condition) = result else {
            panic!("a valid implication carries its bindings: {result:#?}");
        };
        let expected = term(
            &definition,
            "setConcat{}(setItem{}(I:SortInt{}), G2:SortSet{})",
        );
        let (variable, bound) = condition
            .substitution
            .iter()
            .chain(condition.witnesses.iter())
            .find(|(variable, _)| variable.name.starts_with(g.name.as_ref()))
            .expect("the refreshed existential frame is bound");
        assert_eq!(variable.sort, g.sort, "{condition:#?}");
        assert_eq!(bound, &expected, "{condition:#?}");
    }

    fn list_frame_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortList{}
                    [hook{}("LIST.List"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]
                sort SortE{} []
                sort SortS{} []
                sort SortCfg{} []
                hooked-symbol listUnit{}() : SortList{}
                    [function{}(), total{}(), hook{}("LIST.unit")]
                hooked-symbol listItem{}(SortE{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.element")]
                hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{}
                    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]
                symbol a{}() : SortE{} [constructor{}()]
                symbol b{}() : SortE{} [constructor{}()]
                symbol c{}() : SortE{} [constructor{}()]
                symbol end{}() : SortS{} [constructor{}()]
                symbol cfg{}(SortS{}, SortList{}) : SortCfg{} [constructor{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// `cfg(end, ?A [x] ?C)`: the states' list holds `x` somewhere between two existential parts.
    fn item_between_list_parts(definition: &BackendDefinition, item: &str) -> Pattern {
        pattern(
            definition,
            &format!(
                "cfg{{}}(end{{}}(), listConcat{{}}(A:SortList{{}}, listConcat{{}}(listItem{{}}({item}{{}}()), C:SortList{{}})))"
            ),
        )
    }

    fn list_parts_existentials() -> BTreeSet<crate::term::Variable> {
        BTreeSet::from([
            crate::term::Variable::new("A", Sort::simple("SortList")),
            crate::term::Variable::new("C", Sort::simple("SortList")),
        ])
    }

    /// A list value is a finite sequence and concatenation is associative, so `?A [a] ?C`
    /// denotes the lists that hold `a`: `[a, b] L` is one of them, with `?A` the empty list and
    /// `?C` the list after `a`, whatever `L` is.
    #[test]
    fn an_item_between_two_existential_list_parts_is_found_at_its_position() {
        let definition = list_frame_definition();
        let antecedent = pattern(
            &definition,
            "cfg{}(end{}(), listConcat{}(listItem{}(a{}()), listConcat{}(listItem{}(b{}()), L:SortList{})))",
        );
        let consequent = item_between_list_parts(&definition, "a");
        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &list_parts_existentials(),
            &NoSolver,
        )
        .expect("implication should be checked");
        let Coverage::Covered(condition) = result else {
            panic!("the item at a known position covers the state: {result:#?}");
        };
        let witness = |name: &str| {
            condition
                .substitution
                .iter()
                .chain(condition.witnesses.iter())
                .find(|(variable, _)| variable.name.starts_with(name))
                .map(|(_, bound)| bound.clone())
                .unwrap_or_else(|| panic!("{name} is bound: {condition:#?}"))
        };
        assert_eq!(witness("A"), term(&definition, "listUnit{}()"));
        assert_eq!(
            witness("C"),
            term(&definition, "listConcat{}(listItem{}(b{}()), L:SortList{})")
        );

        let verdict = check_implication_with_existentials_complete(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &list_parts_existentials(),
            &NoSolver,
        )
        .expect("implication should be checked");
        assert!(
            matches!(verdict, ImplicationVerdict::Valid(_)),
            "{verdict:#?}"
        );
    }

    /// Every element of a list without a part is at a known position, so an item that matches
    /// none of them is in no instance: `[a, b]` holds no `c`.
    #[test]
    fn an_item_absent_from_a_closed_list_refutes_the_list_consequent() {
        let definition = list_frame_definition();
        let antecedent = pattern(
            &definition,
            "cfg{}(end{}(), listConcat{}(listItem{}(a{}()), listItem{}(b{}())))",
        );
        let consequent = item_between_list_parts(&definition, "c");
        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &list_parts_existentials(),
            &NoSolver,
        )
        .expect("implication should be checked");
        // The remainder's expansion has no branch: its obligation is `false` on every instance.
        let Coverage::PartialCoverage { coverage, .. } = &result else {
            panic!("no position of the closed list holds the item: {result:#?}");
        };
        assert_eq!(coverage.obligations, vec![Predicate::False], "{result:#?}");

        let verdict = check_implication_with_existentials_complete(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &list_parts_existentials(),
            &NoSolver,
        )
        .expect("implication should be checked");
        assert!(
            matches!(verdict, ImplicationVerdict::Invalid { .. }),
            "{verdict:#?}"
        );
    }

    /// An item absent from the known items of `[a, b] L` may be in `L`, so the consequent is
    /// left open, not refuted.
    #[test]
    fn an_item_absent_from_the_items_of_an_open_list_leaves_the_consequent_open() {
        let definition = list_frame_definition();
        let antecedent = pattern(
            &definition,
            "cfg{}(end{}(), listConcat{}(listItem{}(a{}()), listConcat{}(listItem{}(b{}()), L:SortList{})))",
        );
        let consequent = item_between_list_parts(&definition, "c");
        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &list_parts_existentials(),
            &NoSolver,
        )
        .expect("implication should be checked");
        assert!(
            matches!(result, Coverage::Undecided | Coverage::Contingent(_)),
            "{result:#?}"
        );

        let verdict = check_implication_with_existentials_complete(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &list_parts_existentials(),
            &NoSolver,
        )
        .expect("implication should be checked");
        assert!(
            matches!(verdict, ImplicationVerdict::Indeterminate { .. }),
            "{verdict:#?}"
        );
    }

    fn top_simplification_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                sort SortS{} []
                symbol wrap{}(SortInt{}) : SortS{} [constructor{}()]
                symbol plus{}(SortInt{}, SortInt{}) : SortInt{} [function{}()]
                symbol n{}() : SortInt{} [function{}(), total{}(), no-evaluators{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        plus{}(n{}(), n{}()),
                        \and{SortInt{}}(\top{SortInt{}}(), \top{SortInt{}}())
                    )
                ) [label{}("n-plus-n"), simplification{}()]
            endmodule []"#,
        )
        .expect("definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
    }

    /// regression-new issue-2287-simpl-rules-in-kprovex a5: `claim <k> c => 2 #And n +Int n </k>`
    /// with `rule n +Int n => #Top [simplification]`. A simplification rule is an equation of the
    /// definition's theory, so the consequent denotes what its simplified form denotes: under it
    /// `n +Int n` is `\top`, and `2 #And \top` is `2`, which the state `2` implies. The
    /// consequent is simplified with the definition's equations, under the antecedent's
    /// condition, before matching, and the claim holds (#Top).
    #[test]
    fn simplifies_the_consequent_with_the_definition_before_matching() {
        let definition = top_simplification_definition();
        let antecedent = pattern(&definition, r#"wrap{}(\dv{SortInt{}}("2"))"#);
        let consequent = pattern(
            &definition,
            r#"wrap{}(\and{SortInt{}}(\dv{SortInt{}}("2"), plus{}(n{}(), n{}())))"#,
        );

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::new(),
            &NoSolver,
        )
        .expect("implication should be checked");

        assert!(covers_every_instance(&result), "{result:#?}");
    }

    /// Every disjunct of a disjunctive destination is matched in the definition's normal form,
    /// as a single destination is: `wrap(2 #And n +Int n)` denotes `wrap(2)` because the
    /// equation erases its second conjunct, so the antecedent `wrap(2)` lies in the first
    /// disjunct. Matched as written, the conjunct leaves an obligation over `n +Int n` that the
    /// check cannot decide.
    #[test]
    fn simplifies_every_destination_disjunct_with_the_definition_before_matching() {
        let definition = top_simplification_definition();
        let antecedent = pattern(&definition, r#"wrap{}(\dv{SortInt{}}("2"))"#);
        let evaluable = pattern(
            &definition,
            r#"wrap{}(\and{SortInt{}}(\dv{SortInt{}}("2"), plus{}(n{}(), n{}())))"#,
        );
        let other = pattern(&definition, r#"wrap{}(\dv{SortInt{}}("3"))"#);

        let result = check_disjunctive_implication_with_existentials(
            &definition,
            &antecedent,
            &[evaluable, other],
            &BTreeSet::new(),
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("disjunctive implication should be checked");

        assert!(covers_every_instance(&result), "{result:#?}");
    }

    #[test]
    fn eliminates_existential_witnesses_by_substitution() {
        let definition = definition();
        let value = int(&definition, "5");
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        let mut consequent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("5"), \dv{SortInt{}}("5"))"#,
        );
        consequent.constraints.push(Predicate::Equals(
            Term::injection(
                Sort::simple("SortInt"),
                Sort::simple("SortKItem"),
                Term::variable(y.clone()),
            ),
            Term::injection(Sort::simple("SortInt"), Sort::simple("SortKItem"), value),
        ));
        let antecedent = Pattern {
            term: consequent.term.clone(),
            constraints: Vec::new(),
        };

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &NoSolver,
        )
        .expect("implication should be checked");

        assert_single_witness(&result, "Y", &int(&definition, "5"));
        let Coverage::Covered(bindings) = result else {
            panic!("a valid implication carries its bindings: {result:#?}");
        };
        assert!(
            bindings.substitution.is_empty(),
            "obligation witnesses must not leak into the term-match substitution"
        );
    }

    #[test]
    fn witness_elimination_is_iterated() {
        let definition = definition();
        let antecedent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("5"), \dv{SortInt{}}("5"))"#,
        );
        let mut consequent = antecedent.clone();
        let y1 = crate::term::Variable::new("Y1", Sort::simple("SortInt"));
        let y2 = crate::term::Variable::new("Y2", Sort::simple("SortInt"));
        consequent.constraints = vec![
            Predicate::Equals(
                term(&definition, "f{}(Y1:SortInt{})"),
                term(&definition, "f{}(Y2:SortInt{})"),
            ),
            Predicate::Equals(Term::variable(y2.clone()), int(&definition, "5")),
        ];

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y1, y2]),
            &NoSolver,
        )
        .expect("implication should be checked");

        let Coverage::Covered(bindings) = &result else {
            panic!("a valid implication carries its bindings: {result:#?}");
        };
        let witnesses = &bindings.witnesses;
        assert_eq!(witnesses.len(), 2);
        assert!(
            witnesses
                .keys()
                .all(|variable| variable.name.starts_with('Y'))
        );
        assert!(
            witnesses
                .values()
                .all(|value| value == &int(&definition, "5"))
        );
    }

    #[test]
    fn residual_equality_with_an_existential_is_discharged_by_matching() {
        let definition = definition();
        let antecedent = pattern(&definition, "succ{}(X:SortTree{})");
        let mut consequent = antecedent.clone();
        let y = crate::term::Variable::new("Y", Sort::simple("SortTree"));
        consequent.constraints.push(Predicate::Equals(
            term(&definition, "succ{}(Y:SortTree{})"),
            term(&definition, "succ{}(X:SortTree{})"),
        ));

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &NoSolver,
        )
        .expect("implication should be checked");

        assert_single_witness(&result, "Y", &term(&definition, "X:SortTree{}"));
    }

    #[test]
    fn universal_variables_are_never_bound_as_witnesses() {
        let definition = definition();
        let antecedent = pattern(&definition, "X:SortInt{}");
        let mut consequent = antecedent.clone();
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        consequent.constraints.push(Predicate::Equals(
            Term::variable(x),
            Term::variable(y.clone()),
        ));

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &NoSolver,
        )
        .expect("implication should be checked");

        assert_single_witness(&result, "Y", &term(&definition, "X:SortInt{}"));
        let Coverage::Covered(bindings) = result else {
            panic!("a valid implication carries its bindings: {result:#?}");
        };
        assert!(
            bindings.substitution.is_empty(),
            "the universal must not be captured by either substitution"
        );
    }

    #[test]
    fn disjunctive_implication_eliminates_branch_witnesses() {
        let definition = definition();
        let antecedent = pattern(&definition, "X:SortInt{}");
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        let mut witnessed = antecedent.clone();
        witnessed.constraints.push(Predicate::Equals(
            Term::variable(y.clone()),
            Term::variable(x),
        ));
        let alternative = pattern(&definition, r#"\dv{SortInt{}}("0")"#);

        let result = check_disjunctive_implication_with_existentials(
            &definition,
            &antecedent,
            &[witnessed, alternative],
            &BTreeSet::from([y]),
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("disjunctive implication should be checked");

        assert_single_witness(&result, "Y", &term(&definition, "X:SortInt{}"));
    }

    #[test]
    fn invalid_consequent_conditions_retain_the_match_substitution() {
        let definition = definition();
        let antecedent = pattern(&definition, "X:SortInt{}");
        let mut consequent = pattern(&definition, "Y:SortInt{}");
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        consequent
            .constraints
            .push(Predicate::Not(Box::new(Predicate::Equals(
                Term::variable(x.clone()),
                Term::variable(y.clone()),
            ))));

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &NoSolver,
        )
        .unwrap();

        let Coverage::ConditionRefuted { report, .. } = result else {
            panic!("the successful term match is retained: {result:#?}");
        };
        let condition = report.condition();
        assert!(condition.predicates.is_empty());
        assert_eq!(
            condition.substitution.values().collect::<Vec<_>>(),
            [&Term::variable(x)]
        );
    }

    #[test]
    fn applies_the_match_substitution_to_consequent_constraints() {
        let definition = definition();
        let antecedent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("1"))"#,
        );
        let mut consequent = pattern(&definition, r#"pair{}(Y:SortInt{}, Y:SortInt{})"#);
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        consequent.constraints.push(Predicate::Equals(
            Term::variable(y.clone()),
            int(&definition, "1"),
        ));

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &NoSolver,
        )
        .expect("implication should be checked");

        assert!(covers_every_instance(&result), "{result:#?}");
    }

    #[cfg(feature = "z3")]
    #[test]
    fn quantifies_existential_variables_nested_in_smt_terms() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);
        let consequent = pattern(
            &definition,
            r#"pair{}(X:SortInt{}, sub{}(Y:SortInt{}, \dv{SortInt{}}("1")))"#,
        );
        let y = crate::term::Variable::new("Y", Sort::simple("SortInt"));
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = check_implication_with_existentials(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([y]),
            &solver,
        )
        .expect("implication should be checked");

        assert!(covers_every_instance(&result), "{result:#?}");
    }

    #[test]
    fn refreshes_existentials_away_from_antecedent_variables() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        let consequent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));

        assert_eq!(
            check_implication_with_existentials(
                &definition,
                &antecedent,
                &BTreeSet::new(),
                &consequent,
                &BTreeSet::from([x.clone()]),
                &NoSolver,
            ),
            Ok(Coverage::Undecided)
        );
        let result = check_implication_with_existentials_complete(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::from([x]),
            &NoSolver,
        )
        .expect("implication should be checked");
        assert_eq!(result.status(), ImplicationStatus::Indeterminate);
        let condition = result
            .into_condition()
            .expect("the matching subset should be retained");
        assert_eq!(condition.predicates.len(), 1);
        assert!(
            condition
                .substitution
                .keys()
                .all(|variable| variable.name.contains("!exists"))
        );
    }

    #[test]
    fn constructor_mismatch_is_invalid() {
        let definition = definition();
        let antecedent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2"))"#,
        );
        let consequent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("3"))"#,
        );

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Ok(Coverage::TermMismatch)
        );
    }

    #[test]
    fn retries_an_indeterminate_match_after_simplifying_the_antecedent() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"f{}(\dv{SortInt{}}("1"))"#);
        let consequent = pattern(&definition, r#"\dv{SortInt{}}("1")"#);

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Ok(Coverage::Covered(Bindings::default()))
        );
    }

    #[test]
    fn a_vacuous_antecedent_is_answered_by_its_own_variant() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"\dv{SortInt{}}("1")"#);
        let consequent = antecedent.clone();
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Unsat),
            validity: Ok(Validity::Refuted),
        };

        let result = check_implication(&definition, &antecedent, &consequent, &solver).unwrap();
        assert_eq!(result, Coverage::Vacuous);
        let verdict = check_complete(&definition, &antecedent, &consequent, &solver).unwrap();
        assert_eq!(verdict, ImplicationVerdict::VacuouslyValid);
        assert_eq!(
            verdict
                .into_condition()
                .map(|condition| condition.predicates),
            Some(vec![Predicate::False])
        );

        let ordinary = check_implication(&definition, &antecedent, &consequent, &NoSolver).unwrap();
        assert_eq!(ordinary, Coverage::Covered(Bindings::default()));
    }

    #[test]
    fn discharges_residual_consequent_constraints_with_smt() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"X:SortInt{}"#);
        let mut consequent = antecedent.clone();
        consequent.constraints.push(Predicate::Equals(
            Term::variable(crate::term::Variable::new("X", Sort::simple("SortInt"))),
            int(&definition, "1"),
        ));
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Valid),
        };

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &solver),
            Ok(Coverage::Covered(Bindings::default()))
        );

        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Refuted),
        };
        let result = check_implication(&definition, &antecedent, &consequent, &solver)
            .expect("implication should be checked");
        let Coverage::ConditionRefuted { report, .. } = result else {
            panic!("a refuted condition should be retained: {result:#?}");
        };
        assert_eq!(report, MatchReport::refuted(Bindings::default()));
        assert_eq!(report.condition().predicates, vec![Predicate::False]);
    }

    #[cfg(feature = "z3")]
    #[test]
    fn negated_existential_implication_is_invariant_under_bound_variable_renaming() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let constrained = |name: &str, value: &str| {
            let mut result = pattern(&definition, r#"\dv{SortInt{}}("1")"#);
            result
                .constraints
                .push(Predicate::Not(Box::new(Predicate::Exists(
                    Variable::new(name, Sort::simple("SortInt")),
                    Box::new(Predicate::Equals(
                        term(&definition, &format!("opaque{{}}({name}:SortInt{{}})")),
                        int(&definition, value),
                    )),
                ))));
            result
        };
        let left = constrained("X", "0");
        let renamed = constrained("Y", "0");
        for (antecedent, consequent) in [(&left, &renamed), (&renamed, &left)] {
            let result = check_implication(&definition, antecedent, consequent, &solver).unwrap();
            assert!(matches!(result, Coverage::Covered(_)), "{result:?}");
        }
        let different = constrained("Y", "1");
        let result = check_implication(&definition, &left, &different, &solver).unwrap();
        assert!(!covers_every_instance(&result), "{result:?}");
    }

    #[cfg(feature = "z3")]
    #[test]
    fn negated_existential_implication_preserves_free_variables_under_renaming() {
        let definition = definition();
        let solver = Z3Solver::new(&definition).unwrap();
        let constrained = |bound: &str, free: &str| {
            let mut result = pattern(&definition, "pair{}(F:SortInt{}, G:SortInt{})");
            result
                .constraints
                .push(Predicate::Not(Box::new(Predicate::Exists(
                    Variable::new(bound, Sort::simple("SortInt")),
                    Box::new(Predicate::Equals(
                        term(&definition, &format!("opaque{{}}({bound}:SortInt{{}})")),
                        term(&definition, &format!("{free}:SortInt{{}}")),
                    )),
                ))));
            result
        };
        let original = constrained("X", "F");
        let renamed = constrained("Y", "F");
        let distinct = constrained("Y", "G");
        for (antecedent, consequent) in [(&original, &renamed), (&renamed, &original)] {
            let result = check_implication(&definition, antecedent, consequent, &solver).unwrap();
            assert!(matches!(result, Coverage::Covered(_)), "{result:?}");
        }
        for (antecedent, consequent) in [(&original, &distinct), (&distinct, &original)] {
            let result = check_implication(&definition, antecedent, consequent, &solver).unwrap();
            assert!(!covers_every_instance(&result), "{result:?}");
        }
    }

    #[test]
    fn complete_check_uses_smt_counterexamples_without_hiding_solver_uncertainty() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"X:SortInt{}"#);
        let mut consequent = antecedent.clone();
        consequent.constraints.push(Predicate::Equals(
            Term::variable(crate::term::Variable::new("X", Sort::simple("SortInt"))),
            int(&definition, "1"),
        ));
        let counterexample = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Contingent),
        };

        // Both the obligation and its negation are satisfiable: the default check splits the
        // antecedent by the obligation, the complete check refutes the implication.
        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &counterexample),
            Ok(Coverage::Contingent(CoverageCondition::contingent(
                Bindings::default(),
                consequent.constraints.clone(),
            )))
        );
        let result = check_implication_with_existentials_complete(
            &definition,
            &antecedent,
            &BTreeSet::new(),
            &consequent,
            &BTreeSet::new(),
            &counterexample,
        )
        .expect("implication should be checked");
        let ImplicationVerdict::Invalid {
            counterexample: _,
            outside: Some(Outside::ConsequentCondition(report)),
        } = result
        else {
            panic!("the counterexample is shown: {result:#?}");
        };
        assert_eq!(report, MatchReport::contingent(Bindings::default()));
        assert_eq!(report.condition().predicates, Vec::new());

        // An unknown answer establishes neither part, so both checks stay undecided.
        let unknown = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Unknown("timeout".into())),
        };
        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &unknown),
            Ok(Coverage::Undecided)
        );

        let unavailable = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Err(SmtError::Unavailable),
        };
        assert_eq!(
            check_implication_with_existentials_complete(
                &definition,
                &antecedent,
                &BTreeSet::new(),
                &consequent,
                &BTreeSet::new(),
                &unavailable,
            ),
            Ok(ImplicationVerdict::Indeterminate { outside: None })
        );
    }

    #[test]
    fn discharges_symbolic_term_match_equalities_with_smt() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);
        let consequent = pattern(
            &definition,
            r#"pair{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("0"))"#,
        );
        let solver = FixedSolver {
            satisfiability: Ok(Satisfiability::Sat),
            validity: Ok(Validity::Valid),
        };

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &solver),
            Ok(Coverage::Covered(Bindings::default()))
        );
    }

    #[test]
    fn discharges_the_union_of_complementary_consequent_conditions() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, X:SortInt{})"#);
        let zero = int(&definition, "0");
        let x = Term::variable(crate::term::Variable::new("X", Sort::simple("SortInt")));
        let equality = Predicate::Equals(x, zero);
        let mut first = antecedent.clone();
        first.constraints.push(equality.clone());
        let mut second = antecedent.clone();
        second.constraints.push(Predicate::Not(Box::new(equality)));

        #[derive(Clone, Copy, Debug)]
        struct DisjunctionSolver;

        impl SmtSolver for DisjunctionSolver {
            fn is_sat(
                &self,
                _predicates: &[Predicate],
                _substitution: &Substitution,
            ) -> Stoppable<Result<Satisfiability, SmtError>> {
                Ok(Ok(Satisfiability::Sat))
            }

            fn check_predicates(
                &self,
                _known: &[Predicate],
                _substitution: &Substitution,
                checked: &[Predicate],
            ) -> Stoppable<Result<Validity, SmtError>> {
                Ok(
                    if matches!(checked, [Predicate::Or(branches)] if branches.len() == 2) {
                        Ok(Validity::Valid)
                    } else {
                        Ok(Validity::Refuted)
                    },
                )
            }
        }

        for consequent in [&first, &second] {
            let result =
                check_implication(&definition, &antecedent, consequent, &DisjunctionSolver)
                    .expect("implication should be checked");
            let Coverage::ConditionRefuted { report, .. } = result else {
                panic!("each condition alone is refuted: {result:#?}");
            };
            assert_eq!(report, MatchReport::refuted(Bindings::default()));
        }
        assert_eq!(
            check_disjunctive_implication_with_existentials(
                &definition,
                &antecedent,
                &[first, second],
                &BTreeSet::new(),
                SimplificationOptions::default(),
                &DisjunctionSolver,
            ),
            Ok(Coverage::Covered(Bindings::default()))
        );
    }

    #[test]
    fn stable_unresolved_function_match_leaves_a_remainder_obligation() {
        let definition = definition();
        let antecedent = pattern(&definition, r#"f{}(X:SortInt{})"#);
        let consequent = pattern(&definition, r#"f{}(X:SortInt{})"#);
        let other = pattern(&definition, r#"\dv{SortInt{}}("1")"#);

        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &NoSolver),
            Ok(Coverage::Covered(Bindings::default()))
        );
        // `f(X) = 1` is not decided without a solver: the proof policy leaves it undecided, and
        // the complete policy reports it as the condition of its undecided answer.
        assert_eq!(
            check_implication(&definition, &antecedent, &other, &NoSolver),
            Ok(Coverage::Undecided)
        );
        let result = check_complete(&definition, &antecedent, &other, &NoSolver)
            .expect("implication should be checked");
        assert_eq!(result.status(), ImplicationStatus::Indeterminate);
        assert_eq!(
            result
                .into_condition()
                .expect("the matching subset should be retained")
                .predicates
                .len(),
            1,
        );
    }

    #[test]
    fn quantified_variables_do_not_hide_free_variables_in_sibling_predicates() {
        let x = crate::term::Variable::new("X", Sort::simple("SortInt"));
        let x_term = Term::variable(x.clone());
        let predicate = Predicate::And(vec![
            Predicate::Equals(x_term.clone(), x_term.clone()),
            Predicate::Exists(
                x.clone(),
                Box::new(Predicate::Equals(x_term.clone(), x_term)),
            ),
        ]);

        assert_eq!(predicate.free_variables(), BTreeSet::from([x]));
    }

    /// `andInt` is an `smtlib` symbol, which the solver sees as an uninterpreted function, and
    /// `plus` an interpreted `smt-hook`.
    #[cfg(feature = "z3")]
    fn bitwise_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                sort SortKItem{} []
                symbol stay{}(SortInt{}) : SortKItem{} [constructor{}()]
                symbol other{}(SortInt{}) : SortKItem{} [constructor{}()]
                symbol andInt{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), smtlib{}("andInt")]
                symbol plus{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), smt-hook{}("+")]
                sort SortVoid{} []
                sort SortLoop{} []
                sort SortU{} []
                symbol loop{}(SortLoop{}) : SortLoop{} [constructor{}()]
                symbol u{}() : SortU{} [constructor{}()]
                symbol hold{}(SortVoid{}) : SortKItem{} [constructor{}()]
                symbol spin{}(SortLoop{}) : SortKItem{} [constructor{}()]
                symbol keep{}(SortU{}) : SortKItem{} [constructor{}()]
            endmodule []"#,
        )
        .expect("bitwise definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("bitwise definition should internalize")
    }

    /// `head(X)` constrained by `op(X, 1) = value`.
    #[cfg(feature = "z3")]
    fn constrained(definition: &BackendDefinition, head: &str, op: &str, value: &str) -> Pattern {
        Pattern {
            term: term(definition, &format!("{head}{{}}(X:SortInt{{}})")),
            constraints: vec![Predicate::Equals(
                term(
                    definition,
                    &format!(r#"{op}{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("1"))"#),
                ),
                int(definition, value),
            )],
        }
    }

    /// `X &Int 1 = 2` has no integer solution, so `stay(X)` under it is empty and implies
    /// anything. The solver refutes `X &Int 1 = 3` under it by congruence alone, and it answers
    /// the antecedent satisfiable only because `andInt` is uninterpreted: that `Sat` is no
    /// instance, so the refutation cannot be reported as invalid. With the interpreted `plus`
    /// the antecedent `X = 1` is an instance and the answer stays invalid.
    #[cfg(feature = "z3")]
    #[test]
    fn complete_policy_reports_invalid_only_for_an_antecedent_shown_nonempty() {
        let definition = bitwise_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");

        let result = check_complete(
            &definition,
            &constrained(&definition, "stay", "andInt", "2"),
            &constrained(&definition, "stay", "andInt", "3"),
            &solver,
        )
        .expect("implication should be checked");
        assert_eq!(
            result.status(),
            ImplicationStatus::Indeterminate,
            "{result:#?}"
        );
        assert_eq!(
            result.failure(),
            Some(ImplicationFailure::ConsequentCondition),
            "{result:#?}"
        );
        assert_eq!(
            result
                .into_condition()
                .map(|condition| condition.predicates),
            Some(vec![Predicate::False])
        );
        // The proof policy reads the same refutation only as "not covered".
        let result = check_implication(
            &definition,
            &constrained(&definition, "stay", "andInt", "2"),
            &constrained(&definition, "stay", "andInt", "3"),
            &solver,
        )
        .expect("implication should be checked");
        assert!(
            matches!(result, Coverage::ConditionRefuted { .. }),
            "{result:#?}"
        );

        let result = check_complete(
            &definition,
            &constrained(&definition, "stay", "plus", "2"),
            &constrained(&definition, "stay", "plus", "3"),
            &solver,
        )
        .expect("implication should be checked");
        assert_eq!(result.status(), ImplicationStatus::Invalid, "{result:#?}");
        assert_eq!(
            result.failure(),
            Some(ImplicationFailure::ConsequentCondition),
            "{result:#?}"
        );
    }

    /// A term mismatch refutes every instance of the antecedent; it is invalid exactly when the
    /// antecedent has one.
    #[cfg(feature = "z3")]
    #[test]
    fn complete_policy_reports_a_term_mismatch_only_for_an_antecedent_shown_nonempty() {
        let definition = bitwise_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let consequent = pattern(&definition, "other{}(Y:SortInt{})");

        for (op, status) in [
            ("plus", ImplicationStatus::Invalid),
            ("andInt", ImplicationStatus::Indeterminate),
        ] {
            let result = check_complete(
                &definition,
                &constrained(&definition, "stay", op, "2"),
                &consequent,
                &solver,
            )
            .expect("implication should be checked");
            assert_eq!(result.status(), status, "{op}: {result:#?}");
            assert_eq!(
                result.failure(),
                Some(ImplicationFailure::TermMismatch),
                "{op}: {result:#?}"
            );
            assert_eq!(result.into_condition(), None, "{op}");
        }
    }

    /// A contingent answer is a counterexample only where the antecedent with the negated
    /// obligation has an instance: `stay(X) => stay(5)` has `X = 0`, while under the empty
    /// `X &Int 1 = 2` the solver's `Sat` for `X =/= 5` is no instance.
    #[cfg(feature = "z3")]
    #[test]
    fn complete_policy_reports_a_counterexample_only_when_it_is_shown() {
        let definition = bitwise_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let consequent = pattern(&definition, r#"stay{}(\dv{SortInt{}}("5"))"#);

        let result = check_complete(
            &definition,
            &pattern(&definition, "stay{}(X:SortInt{})"),
            &consequent,
            &solver,
        )
        .expect("implication should be checked");
        assert_eq!(result.status(), ImplicationStatus::Invalid, "{result:#?}");

        let result = check_complete(
            &definition,
            &constrained(&definition, "stay", "andInt", "2"),
            &consequent,
            &solver,
        )
        .expect("implication should be checked");
        assert_eq!(
            result.status(),
            ImplicationStatus::Indeterminate,
            "{result:#?}"
        );
        assert!(result.into_condition().is_some());
    }

    /// `A -> \bottom` holds exactly when `A` is empty.
    #[cfg(feature = "z3")]
    #[test]
    fn a_bottom_consequent_is_invalid_only_for_an_antecedent_shown_nonempty() {
        let definition = bitwise_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let antecedent = parse_pattern("stay{}(X:SortInt{})").expect("antecedent should parse");
        let consequent =
            parse_pattern(r#"\bottom{SortKItem{}}()"#).expect("consequent should parse");
        assert_eq!(bottom_antecedent(&antecedent), None);
        assert_eq!(
            special_consequent(&consequent),
            Some(SpecialConsequent::Bottom)
        );

        for (op, status) in [
            ("plus", ImplicationStatus::Invalid),
            ("andInt", ImplicationStatus::Indeterminate),
        ] {
            let result = grade_bottom_consequent(
                &definition,
                &constrained(&definition, "stay", op, "2"),
                &solver,
            )
            .expect("the grading does not stop");
            assert_eq!(result.status(), status, "{op}: {result:#?}");
            assert_eq!(
                result.failure(),
                Some(ImplicationFailure::ConsequentCondition),
                "{op}: {result:#?}"
            );
            assert_eq!(
                result.into_condition(),
                Some(ImplicationCondition {
                    predicates: vec![Predicate::False],
                    substitution: Substitution::new(),
                    witnesses: Substitution::new(),
                }),
                "{op}"
            );
        }

        // `X + 1 = 2 ∧ X + 1 = 3` leaves no instance.
        let mut empty = constrained(&definition, "stay", "plus", "2");
        empty
            .constraints
            .extend(constrained(&definition, "stay", "plus", "3").constraints);
        assert_eq!(
            grade_bottom_consequent(&definition, &empty, &solver)
                .expect("the grading does not stop"),
            ImplicationVerdict::VacuouslyValid
        );
    }

    /// `SortVoid` has no production and every value of `SortLoop` needs another one, so both
    /// are empty; `SortU` has `u()`, and `SortKItem` has `stay(0)`.
    #[cfg(feature = "z3")]
    #[test]
    fn inhabited_sorts_are_the_least_fixed_point_of_value_building_productions() {
        let definition = bitwise_definition();
        for (sort, inhabited) in [
            ("SortVoid", false),
            ("SortLoop", false),
            ("SortU", true),
            ("SortInt", true),
            ("SortKItem", true),
        ] {
            assert_eq!(
                definition.sort_is_inhabited(&Sort::simple(sort)),
                inhabited,
                "{sort}"
            );
        }
    }

    /// A pattern with a free variable of an empty sort denotes nothing, so a term mismatch from
    /// it is no instance outside the consequent; over an inhabited sort it is.
    #[cfg(feature = "z3")]
    #[test]
    fn complete_policy_reports_invalid_only_over_inhabited_variable_sorts() {
        let definition = bitwise_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let consequent = pattern(&definition, "other{}(Y:SortInt{})");
        for (antecedent, status) in [
            ("hold{}(V:SortVoid{})", ImplicationStatus::Indeterminate),
            ("spin{}(L:SortLoop{})", ImplicationStatus::Indeterminate),
            ("keep{}(U:SortU{})", ImplicationStatus::Invalid),
        ] {
            let result = check_complete(
                &definition,
                &pattern(&definition, antecedent),
                &consequent,
                &solver,
            )
            .expect("implication should be checked");
            assert_eq!(result.status(), status, "{antecedent}: {result:#?}");
            assert_eq!(
                result.failure(),
                Some(ImplicationFailure::TermMismatch),
                "{antecedent}: {result:#?}"
            );
        }
    }

    #[cfg(feature = "z3")]
    fn negated(
        definition: &BackendDefinition,
        antecedent: Pattern,
        consequent: &str,
    ) -> ImplicationStatus {
        let solver = Z3Solver::new(definition).expect("Z3 should initialize");
        let consequent = parse_pattern(consequent).expect("consequent should parse");
        check_negated_consequent(
            definition,
            &antecedent,
            &BTreeSet::new(),
            definition.admit_unverified(&consequent, &[]),
            &solver,
        )
        .expect("the check does not stop")
        .expect("the negated consequent should internalize")
        .status()
    }

    /// `A -> \not C` is invalid exactly when `A /\ C` is nonempty and valid exactly when it is
    /// empty.
    #[cfg(feature = "z3")]
    #[test]
    fn a_negated_consequent_is_decided_by_the_conjunction_of_both_sides() {
        let definition = bitwise_definition();
        let plus = |value| {
            format!(
                r#"\and{{SortKItem{{}}}}(
                    stay{{}}(X:SortInt{{}}),
                    \equals{{SortInt{{}}, SortKItem{{}}}}(
                        plus{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("1")),
                        \dv{{SortInt{{}}}}("{value}")
                    )
                )"#
            )
        };
        let not = |pattern: &str| format!(r#"\not{{SortKItem{{}}}}({pattern})"#);
        let x_plus_one_is_two = constrained(&definition, "stay", "plus", "2");

        // `stay(1)` is a common value.
        assert_eq!(
            negated(
                &definition,
                x_plus_one_is_two.clone(),
                &not("stay{}(Y:SortInt{})")
            ),
            ImplicationStatus::Invalid
        );
        assert_eq!(
            negated(&definition, x_plus_one_is_two.clone(), &not(&plus("2"))),
            ImplicationStatus::Invalid
        );
        // Different constructors, and `X + 1 = 2 /\ X + 1 = 3` for the shared `X`, are disjoint.
        assert_eq!(
            negated(
                &definition,
                x_plus_one_is_two.clone(),
                &not("other{}(Y:SortInt{})")
            ),
            ImplicationStatus::Valid
        );
        assert_eq!(
            negated(&definition, x_plus_one_is_two, &not(&plus("3"))),
            ImplicationStatus::Valid
        );
        // The solver's `Sat` for `X &Int 1 = 2` is no common value, and nothing refutes it.
        assert_eq!(
            negated(
                &definition,
                constrained(&definition, "stay", "andInt", "2"),
                &not("stay{}(Y:SortInt{})")
            ),
            ImplicationStatus::Indeterminate
        );
        // A variable of an empty sort has no value to share.
        assert_eq!(
            negated(
                &definition,
                pattern(&definition, "hold{}(V:SortVoid{})"),
                &not("hold{}(W:SortVoid{})")
            ),
            ImplicationStatus::Indeterminate
        );
        // `\exists Y. \not C` is not the negation of `C`.
        assert_eq!(
            negated(
                &definition,
                pattern(&definition, "stay{}(X:SortInt{})"),
                &format!(
                    r#"\exists{{SortKItem{{}}}}(Y:SortInt{{}}, {})"#,
                    not("stay{}(Y:SortInt{})")
                )
            ),
            ImplicationStatus::Indeterminate
        );
    }

    /// A partial `divInt` (no `total` attribute; `smt-hook(div)` gives the solver a total
    /// operation) and a partial uninterpreted `g`, with `axioms` added to the module.
    #[cfg(feature = "z3")]
    fn partial_definition_with(axioms: &str) -> BackendDefinition {
        let syntax = parse_definition(&format!(
            r#"[]
            module MAIN
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                sort SortKItem{{}} []
                symbol pair{{}}(SortInt{{}}, SortInt{{}}) : SortKItem{{}} [constructor{{}}()]
                hooked-symbol leInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.le"), smt-hook{{}}("<=")]
                hooked-symbol neInt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.ne"), smt-hook{{}}("distinct")]
                hooked-symbol addInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                    [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
                hooked-symbol divInt{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
                    [function{{}}(), hook{{}}("INT.tdiv"), smt-hook{{}}("div")]
                symbol g{{}}(SortInt{{}}) : SortInt{{}} [function{{}}()]
                {axioms}
            endmodule []"#
        ))
        .expect("partial definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("partial definition should internalize")
    }

    #[cfg(feature = "z3")]
    fn partial_definition() -> BackendDefinition {
        partial_definition_with("")
    }

    /// `10 /Int X` and `g(X)`, each undefined for some `X`.
    #[cfg(feature = "z3")]
    const PARTIAL_VALUES: [&str; 2] = [
        r#"divInt{}(\dv{SortInt{}}("10"), X:SortInt{})"#,
        r#"g{}(X:SortInt{})"#,
    ];

    /// `value <=Int value +Int 1`, true wherever `value` is defined.
    #[cfg(feature = "z3")]
    fn at_most_its_successor(value: &str) -> String {
        format!(r#"leInt{{}}({value}, addInt{{}}({value}, \dv{{SortInt{{}}}}("1")))"#)
    }

    /// The K Boolean atom `atom` as a predicate: `\equals(true, atom)`.
    #[cfg(feature = "z3")]
    fn holds(definition: &BackendDefinition, atom: &str) -> Predicate {
        Predicate::Equals(
            term(definition, r#"\dv{SortBool{}}("true")"#),
            term(definition, atom),
        )
    }

    /// Ported from `cbc07_probe_consequent_condition_over_a_partial_term` (P1).
    /// `pair(X, 1) → pair(X, 1) ∧ (v <=Int v +Int 1)` fails at an `X` where `v` is undefined:
    /// there the atom is `\equals(true, ⊥) = ⊥`, so the consequent has no instance while the
    /// antecedent has `pair(X, 1)`.
    #[cfg(feature = "z3")]
    #[test]
    fn a_consequent_condition_over_a_partial_term_is_not_valid() {
        let definition = partial_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        let mut answers = Vec::new();
        for value in PARTIAL_VALUES {
            let mut consequent =
                pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
            consequent
                .constraints
                .push(holds(&definition, &at_most_its_successor(value)));
            let proof = check_implication(&definition, &antecedent, &consequent, &solver)
                .expect("implication should be checked");
            let complete = check_complete(&definition, &antecedent, &consequent, &solver)
                .expect("implication should be checked");
            answers.push((value, proof, complete));
        }
        assert!(
            answers.iter().all(|(_, proof, complete)| {
                !covers_every_instance(proof) && complete.status() != ImplicationStatus::Valid
            }),
            "(value, proof, complete): {answers:#?}"
        );
    }

    /// The companion of P1: where the antecedent states `X =/=Int 0` and the definition states
    /// that `I /Int J` is defined wherever `J =/=Int 0`, the consequent's condition holds on every
    /// instance of the antecedent.
    #[cfg(feature = "z3")]
    #[test]
    fn a_consequent_condition_over_a_term_the_antecedent_defines_is_valid() {
        let definition = partial_definition_with(
            r#"axiom{R, Q} \implies{R}(
                    \equals{SortBool{}, R}(
                        neInt{}(J:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                    ),
                    \equals{Q, R}(
                        \ceil{SortInt{}, Q}(divInt{}(I:SortInt{}, J:SortInt{})),
                        \and{Q}(\top{Q}(), \top{Q}())
                    )
                ) [label{}("div-defined"), simplification{}()]"#,
        );
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let mut antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        antecedent.constraints.push(holds(
            &definition,
            r#"neInt{}(X:SortInt{}, \dv{SortInt{}}("0"))"#,
        ));
        let mut consequent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        consequent.constraints.push(holds(
            &definition,
            &at_most_its_successor(PARTIAL_VALUES[0]),
        ));
        let result = check_implication(&definition, &antecedent, &consequent, &solver)
            .expect("implication should be checked");
        assert!(covers_every_instance(&result), "{result:#?}");
        let result = check_complete(&definition, &antecedent, &consequent, &solver)
            .expect("implication should be checked");
        assert_eq!(result.status(), ImplicationStatus::Valid, "{result:#?}");
    }

    /// Ported from `cbc07_probe_existential_witness_over_a_partial_term` (P2).
    /// `pair(X, 1) → ∃E. pair(X, 1) ∧ E = v` fails at an `X` where `v` is undefined: no element
    /// `E` equals `⊥`, so the consequent has no instance there.
    #[cfg(feature = "z3")]
    #[test]
    fn an_existential_witness_over_a_partial_term_is_not_valid() {
        let definition = partial_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let e = Variable::new("E", Sort::simple("SortInt"));
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        let mut answers = Vec::new();
        for value in PARTIAL_VALUES {
            let mut consequent =
                pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
            consequent.constraints.push(Predicate::Equals(
                Term::variable(e.clone()),
                term(&definition, value),
            ));
            let existentials = BTreeSet::from([e.clone()]);
            let proof = check_implication_with_existentials(
                &definition,
                &antecedent,
                &BTreeSet::new(),
                &consequent,
                &existentials,
                &solver,
            )
            .expect("implication should be checked");
            let complete = check_implication_with_existentials_complete(
                &definition,
                &antecedent,
                &BTreeSet::new(),
                &consequent,
                &existentials,
                &solver,
            )
            .expect("implication should be checked");
            answers.push((value, proof, complete));
        }
        assert!(
            answers.iter().all(|(_, proof, complete)| {
                !covers_every_instance(proof) && complete.status() != ImplicationStatus::Valid
            }),
            "(value, proof, complete): {answers:#?}"
        );
    }

    /// Ported from `cbc07_probe_negated_consequent_over_a_partial_term` (P4).
    /// `pair(X, 1) → ¬(pair(X, 1) ∧ ¬(v <=Int v +Int 1))` fails at an `X` where `v` is undefined:
    /// there `¬\equals(true, ⊥)` is `⊤`, so both sides contain `pair(X, 1)`.
    #[cfg(feature = "z3")]
    #[test]
    fn a_negated_consequent_over_a_partial_term_is_not_valid() {
        let definition = partial_definition();
        let antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        let mut answers = Vec::new();
        for value in PARTIAL_VALUES {
            let atom = at_most_its_successor(value);
            let consequent = format!(
                r#"\not{{SortKItem{{}}}}(\and{{SortKItem{{}}}}(
                    pair{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("1")),
                    \not{{SortKItem{{}}}}(
                        \equals{{SortBool{{}}, SortKItem{{}}}}(\dv{{SortBool{{}}}}("true"), {atom})
                    )
                ))"#
            );
            answers.push((value, negated(&definition, antecedent.clone(), &consequent)));
        }
        assert!(
            answers
                .iter()
                .all(|&(_, status)| status != ImplicationStatus::Valid),
            "(value, status): {answers:#?}"
        );
    }

    /// Ported from `cbc07_probe_antecedent_term_states_definedness` (I7).
    /// `pair(X, v) → ∃Y. pair(X, Y) ∧ (Y <=Int Y +Int 1)` holds: the antecedent is empty wherever
    /// `v` is undefined, so the witness `Y := v` is defined on each of its instances.
    #[cfg(feature = "z3")]
    #[test]
    fn an_antecedent_term_defines_the_partial_terms_it_contains() {
        let definition = partial_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let y = Variable::new("Y", Sort::simple("SortInt"));
        let existentials = BTreeSet::from([y]);
        for value in PARTIAL_VALUES {
            let antecedent = pattern(&definition, &format!("pair{{}}(X:SortInt{{}}, {value})"));
            let mut consequent = pattern(&definition, r#"pair{}(X:SortInt{}, Y:SortInt{})"#);
            consequent
                .constraints
                .push(holds(&definition, &at_most_its_successor("Y:SortInt{}")));
            let result = check_implication_with_existentials(
                &definition,
                &antecedent,
                &BTreeSet::new(),
                &consequent,
                &existentials,
                &solver,
            )
            .expect("implication should be checked");
            assert!(covers_every_instance(&result), "{value}: {result:#?}");
            let result = check_implication_with_existentials_complete(
                &definition,
                &antecedent,
                &BTreeSet::new(),
                &consequent,
                &existentials,
                &solver,
            )
            .expect("implication should be checked");
            assert_eq!(
                result.status(),
                ImplicationStatus::Valid,
                "{value}: {result:#?}"
            );
        }
    }

    /// Ported from `cbc07_probe_antecedent_constraint_states_definedness` (I7).
    /// `pair(X, 1) ∧ (0 <=Int g(X)) → pair(X, 1) ∧ (g(X) <=Int g(X) +Int 1)` holds: the
    /// antecedent's own atom is `⊥` wherever `g(X)` is undefined, so it implies `⌈g(X)⌉`.
    #[cfg(feature = "z3")]
    #[test]
    fn an_antecedent_constraint_defines_the_partial_terms_it_contains() {
        let definition = partial_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let value = PARTIAL_VALUES[1];
        let mut antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        antecedent.constraints.push(holds(
            &definition,
            &format!(r#"leInt{{}}(\dv{{SortInt{{}}}}("0"), {value})"#),
        ));
        let mut consequent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        consequent
            .constraints
            .push(holds(&definition, &at_most_its_successor(value)));
        let result = check_implication(&definition, &antecedent, &consequent, &solver)
            .expect("implication should be checked");
        assert!(covers_every_instance(&result), "{result:#?}");
        let result = check_complete(&definition, &antecedent, &consequent, &solver)
            .expect("implication should be checked");
        assert_eq!(result.status(), ImplicationStatus::Valid, "{result:#?}");
    }

    /// A stop observed inside the check is returned with its cause on the outer layer, never
    /// folded into a verdict or a failure. The destination's obligation `f(X) = X` holds by
    /// `identity-f`, so the check covers the state; a check whose request was cancelled, or whose
    /// step deadline passed, before it could simplify the obligation has no answer about it, and
    /// the owner of the stop publishes it.
    #[test]
    fn a_stop_inside_the_check_is_returned_with_its_cause_instead_of_a_verdict() {
        use std::time::Duration;

        use crate::{
            stop::{CancellationToken, StopCause},
            timeout::{StepTimeoutController, StepTimeoutMode, StepTimeoutOptions},
        };

        let definition = definition();
        let antecedent = pattern(&definition, "pair{}(X:SortInt{}, Y:SortInt{})");
        let consequent = Pattern {
            constraints: vec![Predicate::Equals(
                term(&definition, "f{}(X:SortInt{})"),
                term(&definition, "X:SortInt{}"),
            )],
            ..antecedent.clone()
        };
        let check = || {
            super::check_disjunctive_implication_with_existentials(
                &definition,
                &antecedent,
                std::slice::from_ref(&consequent),
                &BTreeSet::new(),
                SimplificationOptions::default(),
                &NoSolver,
            )
            .map_err(Stop::into_cause)
        };
        let stopped = Err;

        let covered = check()
            .expect("an unstopped check has an answer")
            .expect("an unstopped check decides the implication");
        assert!(matches!(covered, Coverage::Covered(_)), "{covered:#?}");

        let token = CancellationToken::new();
        token.cancel();
        assert_eq!(token.scope(check), stopped(StopCause::Cancelled));

        let controller = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        let _step = controller.begin_step();
        assert_eq!(
            check(),
            stopped(StopCause::Deadline(StepTimeoutMode::Manual(Duration::ZERO)))
        );
    }

    /// A map over `Int` keys and values with a constructor cell around it.
    #[cfg(feature = "z3")]
    fn map_frame_definition() -> BackendDefinition {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                hooked-sort SortMap{}
                    [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
                sort SortCfg{} []
                hooked-symbol mapUnit{}() : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.unit")]
                hooked-symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{}
                    [function{}(), total{}(), hook{}("MAP.element")]
                hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{}
                    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
                hooked-symbol inKeys{}(SortInt{}, SortMap{}) : SortBool{}
                    [function{}(), total{}(), hook{}("MAP.in_keys")]
                symbol cfg{}(SortMap{}) : SortCfg{} [constructor{}()]
            endmodule []"#,
        )
        .expect("map frame definition should parse");
        BackendDefinition::internalize(&syntax, "MAIN")
            .expect("map frame definition should internalize")
    }

    /// `cfg(M Map (1 |-> 2))`, under `constraint` (a predicate over `1 in_keys M`).
    #[cfg(feature = "z3")]
    fn map_frame_state(definition: &BackendDefinition, constraint: Predicate) -> Pattern {
        let mut state = pattern(
            definition,
            r#"cfg{}(mapConcat{}(M:SortMap{}, mapItem{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2"))))"#,
        );
        state.constraints.push(constraint);
        state
    }

    /// `1 in_keys M`.
    #[cfg(feature = "z3")]
    const ONE_IN_KEYS: &str = r#"inKeys{}(\dv{SortInt{}}("1"), M:SortMap{})"#;

    /// `cfg(M Map (1 |-> 2)) ∧ ¬(1 in_keys M = false)` has no instance: the concatenation is
    /// defined only where `1` is not a key of `M`, and the constraint keeps exactly the other
    /// valuations. Its constraints alone are satisfiable; the emptiness shows only with the term's
    /// definedness, under which the check decides the consequent's `1 in_keys M` and simplifies it
    /// to `false`. The implication holds vacuously, alone and as one destination of a
    /// disjunction. Reduced from the symbolic map-frame differential case, whose remainder leaf is
    /// such a state.
    #[cfg(feature = "z3")]
    #[test]
    fn an_antecedent_whose_constraints_leave_its_term_undefined_implies_anything() {
        let definition = map_frame_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let antecedent = map_frame_state(
            &definition,
            Predicate::Not(Box::new(Predicate::Equals(
                term(&definition, ONE_IN_KEYS),
                term(&definition, r#"\dv{SortBool{}}("false")"#),
            ))),
        );
        let consequent = map_frame_state(&definition, holds(&definition, ONE_IN_KEYS));
        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &solver),
            Ok(Coverage::Vacuous)
        );
        assert_eq!(
            check_complete(&definition, &antecedent, &consequent, &solver),
            Ok(ImplicationVerdict::VacuouslyValid)
        );
        let mismatched = pattern(&definition, "cfg{}(mapUnit{}())");
        assert_eq!(
            check_disjunctive_implication_with_existentials(
                &definition,
                &antecedent,
                &[consequent, mismatched],
                &BTreeSet::new(),
                SimplificationOptions::default(),
                &solver,
            ),
            Ok(Coverage::Vacuous)
        );
    }

    /// The companion: under `1 in_keys M = false` the same state has instances, and none of them
    /// has `1` among the keys of `M`, so a consequent that requires it is refuted, not vacuous.
    #[cfg(feature = "z3")]
    #[test]
    fn a_map_frame_antecedent_with_instances_still_refutes_its_consequent() {
        let definition = map_frame_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let antecedent = map_frame_state(
            &definition,
            Predicate::Equals(
                term(&definition, ONE_IN_KEYS),
                term(&definition, r#"\dv{SortBool{}}("false")"#),
            ),
        );
        let consequent = map_frame_state(&definition, holds(&definition, ONE_IN_KEYS));
        let proof = check_implication(&definition, &antecedent, &consequent, &solver)
            .expect("implication should be checked");
        assert!(
            matches!(proof, Coverage::ConditionRefuted { .. }),
            "{proof:#?}"
        );
        let complete = check_complete(&definition, &antecedent, &consequent, &solver)
            .expect("implication should be checked");
        assert_ne!(complete.status(), ImplicationStatus::Valid, "{complete:#?}");
    }

    /// `cfg(end, S Set SetItem(1)) ∧ ¬⌈S Set SetItem(1)⌉` states that its own term is undefined,
    /// so it has no instance, although a solver reads the `\ceil` as an opaque atom that the
    /// term's definedness `¬(1 in S)` does not contradict. The simplifier decides the `\ceil`, so
    /// the knowledge simplifies to `false` with or without a solver, and the implication holds
    /// vacuously. Reduced from the symbolic set-frame differential case, whose remainder leaf is
    /// such a state.
    #[test]
    fn an_antecedent_that_states_its_term_undefined_implies_anything() {
        let definition = set_frame_definition();
        let set = r#"setConcat{}(S:SortSet{}, setItem{}(\dv{SortInt{}}("1")))"#;
        let state = format!("cfg{{}}(end{{}}(), {set})");
        let undefined = Predicate::Not(Box::new(Predicate::Ceil(term(&definition, set))));
        let mut antecedent = pattern(&definition, &state);
        antecedent.constraints.push(undefined);
        let mut consequent = pattern(&definition, &state);
        consequent.constraints.push(Predicate::Equals(
            term(&definition, r#"\dv{SortBool{}}("true")"#),
            term(&definition, r#"setIn{}(\dv{SortInt{}}("1"), S:SortSet{})"#),
        ));
        let check = |solver: &dyn SmtSolver| {
            assert_eq!(
                check_implication(&definition, &antecedent, &consequent, solver),
                Ok(Coverage::Vacuous)
            );
            assert_eq!(
                check_complete(&definition, &antecedent, &consequent, solver),
                Ok(ImplicationVerdict::VacuouslyValid)
            );
        };
        check(&NoSolver);
        #[cfg(feature = "z3")]
        check(&Z3Solver::new(&definition).expect("Z3 should initialize"));
    }

    /// `A -> \bottom` holds exactly when `A` is empty, also when only the definedness of its term
    /// shows it: `cfg(M Map (1 |-> 2)) ∧ ¬(1 in_keys M = false)` has no instance, so it implies
    /// `\bottom`. Under `1 in_keys M = false` the same state has instances, every one of them
    /// outside `\bottom`.
    #[cfg(feature = "z3")]
    #[test]
    fn a_bottom_consequent_holds_for_an_antecedent_whose_constraints_leave_its_term_undefined() {
        let definition = map_frame_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let is_false = Predicate::Equals(
            term(&definition, ONE_IN_KEYS),
            term(&definition, r#"\dv{SortBool{}}("false")"#),
        );
        let empty = map_frame_state(&definition, Predicate::Not(Box::new(is_false.clone())));
        assert_eq!(
            grade_bottom_consequent(&definition, &empty, &solver)
                .expect("the grading does not stop"),
            ImplicationVerdict::VacuouslyValid
        );
        let inhabited = map_frame_state(&definition, is_false);
        let verdict = grade_bottom_consequent(&definition, &inhabited, &solver)
            .expect("the grading does not stop");
        assert_ne!(verdict.status(), ImplicationStatus::Valid, "{verdict:#?}");
        assert_eq!(
            verdict.failure(),
            Some(ImplicationFailure::ConsequentCondition),
            "{verdict:#?}"
        );
    }

    /// The same for `cfg(end, S Set SetItem(1)) ∧ ¬⌈S Set SetItem(1)⌉`, whose constraint states
    /// its own term undefined: the simplifier decides the `\ceil`, with or without a solver.
    #[test]
    fn a_bottom_consequent_holds_for_an_antecedent_that_states_its_term_undefined() {
        let definition = set_frame_definition();
        let set = r#"setConcat{}(S:SortSet{}, setItem{}(\dv{SortInt{}}("1")))"#;
        let mut antecedent = pattern(&definition, &format!("cfg{{}}(end{{}}(), {set})"));
        antecedent
            .constraints
            .push(Predicate::Not(Box::new(Predicate::Ceil(term(
                &definition,
                set,
            )))));
        let check = |solver: &dyn SmtSolver| {
            assert_eq!(
                grade_bottom_consequent(&definition, &antecedent, solver)
                    .expect("the grading does not stop"),
                ImplicationVerdict::VacuouslyValid
            );
        };
        check(&NoSolver);
        #[cfg(feature = "z3")]
        check(&Z3Solver::new(&definition).expect("Z3 should initialize"));
    }

    /// `A -> C` holds when every instance of `A` lies in `C`, so an `A` with no instance implies a
    /// consequent whose term it does not match as well. `cfg(M Map (1 |-> 2)) ∧ ¬(1 in_keys M =
    /// false)` has none (see above); its term does not match `cfg(.Map)`. The complete policy
    /// shows no instance outside and then decides the emptiness the mismatch left undecided:
    /// vacuously valid. The proof policy's term mismatch, that no instance lies in the
    /// destination, is true of it too, and is kept. Under `1 in_keys M = false` the state has
    /// instances, all outside `cfg(.Map)`, so the answer is not valid.
    #[cfg(feature = "z3")]
    #[test]
    fn an_empty_antecedent_implies_a_consequent_whose_term_it_does_not_match() {
        let definition = map_frame_definition();
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let is_false = Predicate::Equals(
            term(&definition, ONE_IN_KEYS),
            term(&definition, r#"\dv{SortBool{}}("false")"#),
        );
        let empty = map_frame_state(&definition, Predicate::Not(Box::new(is_false.clone())));
        let mismatched = pattern(&definition, "cfg{}(mapUnit{}())");
        assert_eq!(
            check_complete(&definition, &empty, &mismatched, &solver),
            Ok(ImplicationVerdict::VacuouslyValid)
        );
        assert_eq!(
            check_implication(&definition, &empty, &mismatched, &solver),
            Ok(Coverage::TermMismatch)
        );
        let inhabited = map_frame_state(&definition, is_false);
        let verdict = check_complete(&definition, &inhabited, &mismatched, &solver)
            .expect("implication should be checked");
        assert_ne!(verdict.status(), ImplicationStatus::Valid, "{verdict:#?}");
        assert_eq!(
            verdict.failure(),
            Some(ImplicationFailure::TermMismatch),
            "{verdict:#?}"
        );
    }

    /// The same for `cfg(end, S Set SetItem(1)) ∧ ¬⌈S Set SetItem(1)⌉`, whose emptiness only the
    /// simplifier shows (the solver reads the `\ceil` as an opaque atom), against `cfg(end,
    /// .Set)`, with or without a solver.
    #[test]
    fn an_antecedent_that_states_its_term_undefined_implies_a_mismatched_consequent() {
        let definition = set_frame_definition();
        let set = r#"setConcat{}(S:SortSet{}, setItem{}(\dv{SortInt{}}("1")))"#;
        let mut antecedent = pattern(&definition, &format!("cfg{{}}(end{{}}(), {set})"));
        antecedent
            .constraints
            .push(Predicate::Not(Box::new(Predicate::Ceil(term(
                &definition,
                set,
            )))));
        let mismatched = pattern(&definition, "cfg{}(end{}(), setUnit{}())");
        let check = |solver: &dyn SmtSolver| {
            assert_eq!(
                check_complete(&definition, &antecedent, &mismatched, solver),
                Ok(ImplicationVerdict::VacuouslyValid)
            );
        };
        check(&NoSolver);
        #[cfg(feature = "z3")]
        check(&Z3Solver::new(&definition).expect("Z3 should initialize"));
    }

    /// `A -> \not C` holds when `A /\ C` is empty, which an empty `A` makes it. The conjunction of
    /// `cfg(end, S Set SetItem(1)) ∧ ¬⌈S Set SetItem(1)⌉` with `cfg(end, T)` binds `T` to the
    /// undefined set; only the simplifier shows that its constraints contradict the definedness
    /// of the binding, so the solver alone leaves the conjunction undecided.
    #[test]
    fn a_negated_consequent_holds_for_an_antecedent_that_states_its_term_undefined() {
        let definition = set_frame_definition();
        let set = r#"setConcat{}(S:SortSet{}, setItem{}(\dv{SortInt{}}("1")))"#;
        let mut antecedent = pattern(&definition, &format!("cfg{{}}(end{{}}(), {set})"));
        antecedent
            .constraints
            .push(Predicate::Not(Box::new(Predicate::Ceil(term(
                &definition,
                set,
            )))));
        let consequent =
            parse_pattern(r"\not{SortCfg{}}(cfg{}(end{}(), T:SortSet{}))").expect("should parse");
        let check = |solver: &dyn SmtSolver| {
            assert_eq!(
                check_negated_consequent(
                    &definition,
                    &antecedent,
                    &BTreeSet::new(),
                    definition.admit_unverified(&consequent, &[]),
                    solver,
                )
                .expect("the check does not stop")
                .expect("the negated consequent should internalize")
                .status(),
                ImplicationStatus::Valid
            );
        };
        check(&NoSolver);
        #[cfg(feature = "z3")]
        check(&Z3Solver::new(&definition).expect("Z3 should initialize"));
    }

    /// `pair(X, 1) ∧ h(X) <=Int 0 ∧ 1 <=Int X`, where the equation `h(X) = X` makes the
    /// constraints contradictory, has no instance; the solver, reading `h` as an uninterpreted
    /// function, answers its consequent condition `X <=Int 5` contingent on the knowledge as
    /// written. The check's refutation by simplification decides `knowledge ∧ ¬(X <=Int 5)`
    /// after evaluating `h`, finds it contradictory and so shows the consequent to hold: a
    /// contradiction of the knowledge that only the simplifier exposes is found before a
    /// contingent answer is graded, which is why a contingent match is not decided again for
    /// emptiness.
    #[cfg(feature = "z3")]
    #[test]
    fn an_antecedent_contradictory_only_once_simplified_is_covered_before_it_is_contingent() {
        let definition = partial_definition_with(
            r#"symbol h{}(SortInt{}) : SortInt{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        h{}(X:SortInt{}),
                        \and{SortInt{}}(X:SortInt{}, \top{SortInt{}}())
                    )
                ) [label{}("identity-h"), simplification{}()]"#,
        );
        let solver = Z3Solver::new(&definition).expect("Z3 should initialize");
        let mut antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        antecedent.constraints.push(holds(
            &definition,
            r#"leInt{}(h{}(X:SortInt{}), \dv{SortInt{}}("0"))"#,
        ));
        antecedent.constraints.push(holds(
            &definition,
            r#"leInt{}(\dv{SortInt{}}("1"), X:SortInt{})"#,
        ));
        let mut consequent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        consequent.constraints.push(holds(
            &definition,
            r#"leInt{}(X:SortInt{}, \dv{SortInt{}}("5"))"#,
        ));
        assert_eq!(
            solver
                .check_predicates(
                    &pattern_knowledge(&definition, &antecedent),
                    &Substitution::new(),
                    &consequent.constraints,
                )
                .expect("the query does not stop"),
            Ok(Validity::Contingent)
        );
        let result = check_implication(&definition, &antecedent, &consequent, &solver)
            .expect("implication should be checked");
        assert!(covers_every_instance(&result), "{result:#?}");
        let result = check_complete(&definition, &antecedent, &consequent, &solver)
            .expect("implication should be checked");
        assert_eq!(result.status(), ImplicationStatus::Valid, "{result:#?}");
    }

    /// A contingent match is graded as the check established it: the antecedent's knowledge is
    /// not simplified and decided again. The solver answers every satisfiability query `Sat`
    /// and the consequent condition contingent; the check asks for the satisfiability of the
    /// constraints, then for that of the knowledge with the negated condition (the refutation by
    /// simplification), and nothing more.
    #[test]
    fn a_contingent_match_is_not_decided_again_for_emptiness() {
        struct Counting {
            is_sat: std::cell::Cell<usize>,
        }
        impl SmtSolver for Counting {
            fn is_sat(
                &self,
                _predicates: &[Predicate],
                _substitution: &Substitution,
            ) -> Stoppable<Result<Satisfiability, SmtError>> {
                self.is_sat.set(self.is_sat.get() + 1);
                Ok(Ok(Satisfiability::Sat))
            }

            fn check_predicates(
                &self,
                _known: &[Predicate],
                _substitution: &Substitution,
                _checked: &[Predicate],
            ) -> Stoppable<Result<Validity, SmtError>> {
                Ok(Ok(Validity::Contingent))
            }
        }
        let definition = definition();
        let solver = Counting {
            is_sat: std::cell::Cell::new(0),
        };
        let mut antecedent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        antecedent
            .constraints
            .push(Predicate::Not(Box::new(Predicate::Equals(
                term(&definition, "X:SortInt{}"),
                int(&definition, "7"),
            ))));
        let obligation = Predicate::Equals(int(&definition, "0"), term(&definition, "X:SortInt{}"));
        let mut consequent = pattern(&definition, r#"pair{}(X:SortInt{}, \dv{SortInt{}}("1"))"#);
        consequent.constraints.push(obligation.clone());
        assert_eq!(
            check_implication(&definition, &antecedent, &consequent, &solver),
            Ok(Coverage::Contingent(CoverageCondition::contingent(
                Bindings::default(),
                vec![obligation],
            )))
        );
        assert_eq!(solver.is_sat.get(), 2);
    }
}
