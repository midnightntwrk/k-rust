//! A pattern-slot kill requires a proved difference in the state sequences of the two runs, unless a state slot distinguishes on the same test. An unproved pattern disagreement becomes Unknown.
//!
//! Each sequence records the before state of every committed Rewrite transition and the leaf state. Remainder entries add no position; rule identities, effects, and halt depth are not difference evidence.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::backend::{Backend, BackendError};
use k_rust::kore::ast::Pattern;
use k_rust_backend::definition::{BackendDefinition, SortInfo};
use k_rust_backend::matching::SortGraph;
use k_rust_backend::rule::Predicate;
use k_rust_backend::smt::{Satisfiability, SmtSolver};
use k_rust_backend::stop::StopCause;
use k_rust_backend::substitution::Substitution;
use k_rust_backend::term::{Name, Sort, Symbol, Term, TermKind, Variable, VariableKind};
use k_rust_backend::unification::{UnificationResult, unify_term_pairs};

use crate::{
    execution::HaltClass,
    feasibility::{
        Inhabitation, InitialVariables, LeafFeasibility, free_constructor, interpreted_predicate,
        proves_clash, solver_answer, translates_exactly,
    },
};

/// One path's states; its rewrite length is `states.len() - 1`, never its halt depth.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateSequence {
    /// The leaf's halt class.
    pub halt: HaltClass,
    /// Rewrite before states in order, followed by the leaf state.
    pub states: Vec<Pattern>,
    /// Whether the leaf has a proved instance.
    pub feasibility: LeafFeasibility,
}

/// State sequences of all leaves, in backend leaf order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct StateSequences {
    /// One sequence for each path-set leaf.
    pub leaves: Vec<StateSequence>,
}

/// The side supplying a difference witness.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CertifiedSide {
    /// The baseline definition.
    Baseline,
    /// The mutant-side definition that ran.
    Mutant,
}

/// A reason a covering path cannot equal the witness path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Exclusion {
    /// The covering leaf has no feasible instance.
    Vacuous,
    /// Complete path lengths rule out equality.
    Length,
    /// Generalized states have a proved constructor clash.
    Clash,
    /// Stable-variable path conditions are provably disjoint.
    Disjoint,
}

/// Why a difference was not proved; none of these reasons permits a kill.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NotProvedReason {
    /// The two definitions' signature projections differ.
    SignatureDiffers,
    /// Neither side has a covering set of leaves.
    NotCovering,
    /// No feasible path excludes every path on the other side.
    NoWitness,
    /// A state could not be internalized for proof.
    Internalization,
    /// A transition was unexpected or a committed rewrite was not reported.
    Unobservable,
    /// The sequence run's branch identities differ from the primary run.
    BranchMismatch,
    /// The sequence run's watchdog fired.
    Timeout,
    /// The backend failed, returned an inadmissible halt, or could not decode a state.
    Backend,
}

/// A proved difference or the reason the proof failed closed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DifferenceCertificate {
    /// This feasible leaf differs from every leaf on the other side.
    Proved {
        /// The side supplying the witness.
        witness_side: CertifiedSide,
        /// The witness index in leaf order.
        witness_leaf: usize,
        /// One exclusion for each leaf of the covering side, in leaf order.
        exclusions: Vec<Exclusion>,
    },
    /// No execution difference was proved.
    NotProved(NotProvedReason),
}

impl From<BackendError> for NotProvedReason {
    /// A backend error while reading a definition or deciding a proof fails closed.
    fn from(_: BackendError) -> Self {
        Self::Backend
    }
}

impl From<StopCause> for NotProvedReason {
    /// A stopped solver operation fails closed.
    fn from(_: StopCause) -> Self {
        Self::Backend
    }
}

/// The part of a symbol declaration that the certificate relies on: its sorts, whether it is a
/// free constructor, and its hook.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SymbolShape {
    /// The symbol's sort parameters.
    pub sort_variables: Vec<Name>,
    /// The argument sorts.
    pub argument_sorts: Vec<Sort>,
    /// The result sort.
    pub result_sort: Sort,
    /// Whether the symbol is a constructor of K's free term algebra
    /// (`feasibility::free_constructor`).
    pub free: bool,
    /// The builtin hook, whose meaning does not depend on the definition.
    pub hook: Option<Name>,
}

/// The constructor, sort, subsort and hook structure of a definition: exactly what the proofs of
/// `Clash` and `Disjoint` assume means the same on both sides.
///
/// The full symbol table is not compared: withdrawing claims strips `total`, `functional`,
/// `injective`, `smt-hook` and `smtlib` from productions, so the tables of a withdrawn side
/// differ from the baseline's without any change to this projection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignatureProjection {
    /// The declared sorts.
    pub sorts: BTreeMap<Name, SortInfo>,
    /// The subsort closure, which gives injections their meaning.
    pub sort_graph: SortGraph,
    /// The shape of every symbol, by name.
    pub symbols: BTreeMap<Name, SymbolShape>,
}

impl SignatureProjection {
    fn of(definition: &BackendDefinition) -> Self {
        Self {
            sorts: definition.sorts().clone(),
            sort_graph: definition.sort_graph().clone(),
            symbols: definition
                .symbols()
                .iter()
                .map(|(name, symbol)| (name.clone(), SymbolShape::of(symbol)))
                .collect(),
        }
    }
}

impl SymbolShape {
    fn of(symbol: &Symbol) -> Self {
        Self {
            sort_variables: symbol.sort_variables.clone(),
            argument_sorts: symbol.argument_sorts.clone(),
            result_sort: symbol.result_sort.clone(),
            free: free_constructor(symbol),
            hook: symbol.attributes.hook.clone(),
        }
    }
}

/// What the certificate needs to know about one side's definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DefinitionFacts {
    /// The signature projection compared between the sides.
    pub signature: SignatureProjection,
}

/// The facts of the default module of `backend`. A backend error is `Backend`.
pub fn definition_facts(backend: &mut Backend) -> Result<DefinitionFacts, NotProvedReason> {
    backend.with_solver(None, |definition, _| {
        Ok(DefinitionFacts {
            signature: SignatureProjection::of(definition),
        })
    })
}

/// Proves that some ground instance of `initial` executes differently on the two sides.
///
/// `backend` is the baseline's; every state of both sides is internalized in its definition,
/// and a `Disjoint` query is asked of its solver.
///
/// **Rule.** If the signature projections differ, the result is `SignatureDiffers`. Every
/// state is generalized, scoped per side, leaf and position: free constructors, injections and
/// domain values are kept; *stable* variables are kept; every other element variable is renamed
/// consistently within the scope, to a scope variable whose name is no stable variable's
/// (`Scope::fresh`); every other subterm (a non-free application, a set variable, a
/// collection, a conjunction) becomes a fresh wildcard variable of its sort, one per
/// occurrence. The stable variables are the test's initial variables (`InitialVariables`: the
/// free variables of `initial` when every one of them internalizes to an element variable of
/// an inhabited sort, and none otherwise). A leaf's predicate conjuncts (its `pc`, from the
/// leaf state) are kept apart and never generalized. A covering-side path `q` excludes a
/// witness path `p` by the first of: `Vacuous` (`q` halts Vacuous or is Unsat), `Length` (on
/// positions `states.len() - 1`: `q` terminal and shorter, or `p` terminal and `q` longer),
/// `Clash` (a clash that `proves_clash` certifies in the joint unification of the generalized
/// states at every common position) and `Disjoint` (both pcs non-empty, a non-empty stable
/// set, only stable variables, only hooked, free-constructor, injection and domain-value
/// symbols, an exact SMT translation, and a solver `Unsat` for their conjunction). A side is
/// covering when it has a leaf and every leaf halts Stuck, Trivial, Vacuous, Indeterminate or
/// DepthBound; a witness is a leaf that is not Vacuous and is Syntactic or Solver feasible.
/// With the mutant, then the baseline, as the witness side and the other side covering, the
/// first witness in leaf order that every covering leaf excludes is `Proved`, with one
/// exclusion per covering leaf in leaf order. Otherwise the result is `NotCovering` when
/// neither direction was attempted, `Internalization` when a leaf failed to internalize, and
/// `NoWitness` otherwise; a backend error is `Backend`.
///
/// **Claim.** `Proved` means that some ground instance σ of `initial` has, as the two
/// definitions execute in k-rust, a witness-side state sequence that no covering-side sequence
/// equals.
///
/// **Proof.** Every state is read under k-rust's variable-identity contract
/// (`feasibility`'s VARIABLE_IDENTITY == 3 assertion, T-VI): names are read verbatim;
/// injective printing and binder renaming preserve the state and pc up to a bijective
/// renaming that fixes initial names. One growing counter skips every request spelling.
/// Unbound-result equation instances are unused and diagnosed (BackendLimit in the bridge).
/// Within the request that produced the state one name is
/// one variable, no minted variable has a request variable's name, and a request variable
/// keeps its meaning in every state of every path. Both sides' runs are requests whose input
/// is `initial`, so their only shared names are its variables. The witness `p` is feasible, so
/// some θ satisfies its pc; let σ be θ restricted to the variables of `initial`. k-rust keeps
/// every condition it relied on in the leaf predicate, so θ follows `p`: σ has a witness-side
/// sequence `S` whose states `0..=n_p` are instances of `p`'s states, ending there if `p` is
/// terminal. If the covering side had a σ-sequence `S' = S`, then, because strategy `all`
/// with PathSet leaves covers the initial state and the covering condition excludes breadth
/// bounds, cancellation and errors, `S'` follows some covering path `q` under a θ' that agrees
/// with σ on the initial variables. Each exclusion contradicts `S' = S`. `Vacuous`: `q` has no
/// instance (its halt, or a solver `Unsat` for its real pc). `Length`: a Stuck or Trivial leaf
/// has no defined successor, so the lengths differ. `Clash`: equal states at every common
/// position would be a common solution of the generalized equations. Each wildcard takes the
/// value it hides; each scope variable the value of the one variable it renames, which is one
/// value because within one state a name is one variable; each stable variable its σ value on
/// both sides, because it is a request variable of both runs. No two of these are identified
/// by accident: a scope variable is new in its scope, different scopes have different
/// prefixes, and no scope variable has a stable variable's name. A certified clash has no
/// solution in K's free-constructor algebra, which means the same on both sides because the
/// projections are equal. Scopes are per position, so no valuation of a minted variable across
/// positions or paths is assumed (ticket VI-T01). `Disjoint`: σ satisfies both pcs because
/// they mention only stable variables, their symbols mean the same in both definitions, and
/// the translation is exact, so the solver's `Unsat` contradicts σ. Every covering path is
/// excluded, so no covering-side sequence from σ equals `S`.
///
/// Positions count Rewrite transitions, so a Stuck and a Trivial leaf at the same state have
/// the same length: the certificate never separates a Stuck end from an undefined step
/// (EI-T05). Duplicate paths, leaf order and which rule fired are not evidence.
///
/// **Trust base.** k-rust's `all`-mode coverage, symbolic soundness and feasibility contracts
/// (every symbolic verdict trusts them) and its variable-identity contract (version 3, asserted
/// at compile time and pinned by `tests/name_identity.rs`); the unifier's clash soundness
/// (`proves_clash`, as `BackendRelations`); solver `Unsat` and the consistency of the
/// baseline's smt-lemmas, which a `Disjoint` query asserts. A mutant-side witness's feasibility
/// is decided under that side's supported lemmas only; on a patched ground run, lemmas the
/// mutant inserted are trusted in that side's normal forms, and a lemma headed by a
/// constructor, which contradicts freeness, is not seen by `Clash` (the state oracle has the
/// same trust). A covering leaf's `Unsat` is decided by the backend of the side that ran it,
/// under that side's supported lemmas: a `Vacuous` exclusion of a mutant-side leaf trusts the
/// mutant's lemmas as that side's `Vacuous` halts and its feasibility already do. The
/// sequences' branch check relies on k-rust running one request deterministically, and fails
/// closed if it does not.
///
/// A failure never proves anything: every failure is `NotProved`, which can only turn a
/// pattern-slot `Distinguish` into `Unknown`.
pub fn certify_difference(
    backend: &mut Backend,
    initial: &Pattern,
    baseline_facts: &DefinitionFacts,
    mutant_facts: &DefinitionFacts,
    baseline_sequences: &StateSequences,
    mutant_sequences: &StateSequences,
) -> DifferenceCertificate {
    if baseline_facts.signature != mutant_facts.signature {
        return DifferenceCertificate::NotProved(NotProvedReason::SignatureDiffers);
    }
    backend
        .with_solver(None, |definition, solver| {
            Ok::<_, NotProvedReason>(
                Prover::new(definition, solver, initial)
                    .certify(baseline_sequences, mutant_sequences),
            )
        })
        .unwrap_or_else(DifferenceCertificate::NotProved)
}

/// The baseline definition and solver, with the stable variables of one initial state.
struct Prover<'a> {
    definition: &'a BackendDefinition,
    solver: &'a dyn SmtSolver,
    stable: BTreeSet<Variable>,
}

/// One leaf prepared for the exclusions.
struct Leaf<'s> {
    sequence: &'s StateSequence,
    /// `states.len() - 1`; `None` for a sequence without states, which is never a witness.
    positions: Option<usize>,
    /// The generalized states and the leaf's pc; `None` when a state failed to internalize.
    internal: Option<Internal>,
}

/// A leaf's generalized states, in position order, and its predicate conjuncts.
struct Internal {
    terms: Vec<Term>,
    pc: Vec<Predicate>,
}

impl<'a> Prover<'a> {
    /// The stable variables are the test's initial variables, or none.
    fn new(
        definition: &'a BackendDefinition,
        solver: &'a dyn SmtSolver,
        initial: &Pattern,
    ) -> Self {
        let stable = InitialVariables::of(definition, &Inhabitation::of(definition), initial)
            .unwrap_or_default();
        Self {
            definition,
            solver,
            stable,
        }
    }

    fn certify(&self, baseline: &StateSequences, mutant: &StateSequences) -> DifferenceCertificate {
        let baseline = self.leaves('B', baseline);
        let mutant = self.leaves('M', mutant);
        let mut attempted = false;
        for (side, witnesses, others) in [
            (CertifiedSide::Mutant, &mutant, &baseline),
            (CertifiedSide::Baseline, &baseline, &mutant),
        ] {
            if others.is_empty() || !others.iter().all(|leaf| covering(leaf.sequence.halt)) {
                continue;
            }
            attempted = true;
            for (index, witness) in witnesses.iter().enumerate() {
                if !is_witness(witness) {
                    continue;
                }
                if let Some(exclusions) = others
                    .iter()
                    .map(|other| self.excludes(other, witness))
                    .collect::<Option<Vec<_>>>()
                {
                    return DifferenceCertificate::Proved {
                        witness_side: side,
                        witness_leaf: index,
                        exclusions,
                    };
                }
            }
        }
        let reason = if !attempted {
            NotProvedReason::NotCovering
        } else if baseline
            .iter()
            .chain(&mutant)
            .any(|leaf| leaf.internal.is_none())
        {
            NotProvedReason::Internalization
        } else {
            NotProvedReason::NoWitness
        };
        DifferenceCertificate::NotProved(reason)
    }

    fn leaves<'s>(&self, side: char, sequences: &'s StateSequences) -> Vec<Leaf<'s>> {
        sequences
            .leaves
            .iter()
            .enumerate()
            .map(|(index, sequence)| Leaf {
                sequence,
                positions: sequence.states.len().checked_sub(1),
                internal: self.internalize(side, index, sequence),
            })
            .collect()
    }

    /// Every state of `sequence` internalized in the baseline definition and generalized in
    /// its own scope; the pc is the leaf state's.
    fn internalize(&self, side: char, leaf: usize, sequence: &StateSequence) -> Option<Internal> {
        let mut terms = Vec::with_capacity(sequence.states.len());
        let mut pc = Vec::new();
        for (position, state) in sequence.states.iter().enumerate() {
            let pattern = self
                .definition
                .admit_unverified(state, &[])
                .internalize_pattern()
                .ok()?;
            let mut scope = Scope {
                stable: &self.stable,
                prefix: format!("EI!{side}{leaf}.{position}"),
                renamed: BTreeMap::new(),
                fresh: 0,
            };
            terms.push(scope.generalize(&pattern.term));
            pc = pattern.constraints;
        }
        (!terms.is_empty()).then_some(Internal { terms, pc })
    }

    /// The first exclusion of `witness` by the covering-side leaf `other`, in the order
    /// Vacuous, Length, Clash, Disjoint.
    fn excludes(&self, other: &Leaf<'_>, witness: &Leaf<'_>) -> Option<Exclusion> {
        let (p, q) = (witness.sequence, other.sequence);
        if q.halt == HaltClass::Vacuous || q.feasibility == LeafFeasibility::Unsat {
            return Some(Exclusion::Vacuous);
        }
        let (n_p, n_q) = (witness.positions?, other.positions?);
        if (terminal(q.halt) && n_p > n_q) || (terminal(p.halt) && n_q > n_p) {
            return Some(Exclusion::Length);
        }
        let (Some(p), Some(q)) = (&witness.internal, &other.internal) else {
            return None;
        };
        let pairs =
            (0..=n_p.min(n_q)).map(|index| (p.terms[index].clone(), q.terms[index].clone()));
        if let UnificationResult::Bottom(failure) =
            unify_term_pairs(self.definition, Substitution::new(), pairs)
            && proves_clash(&failure)
        {
            return Some(Exclusion::Clash);
        }
        self.disjoint(p, q).then_some(Exclusion::Disjoint)
    }

    /// Both pcs are non-empty, mention only stable variables and definition-independent
    /// symbols, translate exactly, and the solver answers `Unsat` for their conjunction.
    fn disjoint(&self, p: &Internal, q: &Internal) -> bool {
        if p.pc.is_empty() || q.pc.is_empty() || self.stable.is_empty() {
            return false;
        }
        let query = p.pc.iter().chain(&q.pc).cloned().collect::<Vec<_>>();
        query.iter().all(|predicate| {
            predicate.free_variables().is_subset(&self.stable) && interpreted_predicate(predicate)
        }) && translates_exactly(&query)
            && matches!(
                solver_answer(self.solver, &query),
                Some(Satisfiability::Unsat)
            )
    }
}

/// The generalization scope of one state of one leaf of one side.
struct Scope<'a> {
    stable: &'a BTreeSet<Variable>,
    /// `EI!{side}{leaf}.{position}`: unique per scope, so two scopes never generate one name.
    prefix: String,
    renamed: BTreeMap<Variable, Variable>,
    fresh: usize,
}

impl Scope<'_> {
    /// A variable new to this scope whose name is the name of no stable variable, whatever the
    /// stable variables are called. A decoded initial name can contain `!` (the wire name
    /// `EI-bB0-b1` decodes to `EI!B0!1`); the prefix's `.` is in no decoded name, but the
    /// disjointness rests on this check, not on the name alphabet.
    fn fresh(&mut self, sort: Sort) -> Variable {
        loop {
            self.fresh += 1;
            let name = format!("{}!{}", self.prefix, self.fresh);
            if !self
                .stable
                .iter()
                .any(|variable| *variable.name == *name.as_str())
            {
                return Variable::new(name, sort);
            }
        }
    }

    fn generalize(&mut self, term: &Term) -> Term {
        match term.kind() {
            TermKind::Variable(variable)
                if variable.kind == VariableKind::Element && self.stable.contains(variable) =>
            {
                term.clone()
            }
            TermKind::Variable(variable) if variable.kind == VariableKind::Element => {
                let renamed = match self.renamed.get(variable) {
                    Some(renamed) => renamed.clone(),
                    None => {
                        let renamed = self.fresh(variable.sort.clone());
                        self.renamed.insert(variable.clone(), renamed.clone());
                        renamed
                    }
                };
                Term::variable(renamed)
            }
            TermKind::DomainValue { .. } => term.clone(),
            TermKind::Injection {
                source,
                target,
                term: inner,
            } => Term::injection(source.clone(), target.clone(), self.generalize(inner)),
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } if free_constructor(symbol) => Term::application(
                symbol.clone(),
                sort_arguments.clone(),
                arguments
                    .iter()
                    .map(|argument| self.generalize(argument))
                    .collect(),
            ),
            TermKind::Variable(_)
            | TermKind::Application { .. }
            | TermKind::And(..)
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. } => Term::variable(self.fresh(term.sort())),
        }
    }
}

/// A leaf with no defined successor for its instances.
const fn terminal(halt: HaltClass) -> bool {
    matches!(halt, HaltClass::Stuck | HaltClass::Trivial)
}

/// A halt that keeps the leaves' coverage of the initial state (README 6.3).
const fn covering(halt: HaltClass) -> bool {
    matches!(
        halt,
        HaltClass::Stuck
            | HaltClass::Trivial
            | HaltClass::Vacuous
            | HaltClass::Indeterminate
            | HaltClass::DepthBound
    )
}

/// A leaf that has an instance and at least one state.
fn is_witness(leaf: &Leaf<'_>) -> bool {
    leaf.sequence.halt != HaltClass::Vacuous
        && matches!(
            leaf.sequence.feasibility,
            LeafFeasibility::Syntactic | LeafFeasibility::Solver
        )
        && leaf.positions.is_some()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Under variable identity a decoded name can contain `!`, so a stable variable can have
    /// the name of the first scope candidate. The scope never returns a stable variable's name,
    /// whatever its sort, and renames every other element variable consistently, apart from
    /// the stable names (variable-identity README 5.4 and 7 item 4).
    #[test]
    fn scope_names_avoid_stable_variables() {
        let int = Sort::simple("SortInt");
        let forged = Variable::new("EI!B0.0!1", Sort::simple("SortBool"));
        let stable = BTreeSet::from([forged.clone(), Variable::new("EI!B0.0!2", int.clone())]);
        let mut scope = Scope {
            stable: &stable,
            prefix: "EI!B0.0".into(),
            renamed: BTreeMap::new(),
            fresh: 0,
        };
        let first = scope.fresh(int.clone());
        assert_eq!(first, Variable::new("EI!B0.0!3", int.clone()));
        assert!(stable.iter().all(|variable| variable.name != first.name));
        let x = Term::variable(Variable::new("X", int.clone()));
        let renamed = scope.generalize(&x);
        assert_eq!(
            renamed,
            Term::variable(Variable::new("EI!B0.0!4", int.clone()))
        );
        assert_eq!(
            scope.generalize(&x),
            renamed,
            "one variable, one scope variable"
        );
        let kept = Term::variable(forged);
        assert_eq!(scope.generalize(&kept), kept, "a stable variable is kept");
    }
}
