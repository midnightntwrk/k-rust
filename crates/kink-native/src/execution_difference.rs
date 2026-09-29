//! A pattern-slot kill requires a proved difference in the state sequences of the two runs, unless a state slot distinguishes on the same test. An unproved pattern disagreement becomes Unknown.
//!
//! Each sequence records the before state of every committed Rewrite transition and the leaf state. Remainder entries add no position; rule identities, effects, and halt depth are not difference evidence.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::backend::{Backend, BackendError};
use k_rust::kore::ast::Pattern;
use k_rust_backend::definition::{BackendDefinition, SortInfo};
use k_rust_backend::matching::SortGraph;
use k_rust_backend::rule::Predicate;
use k_rust_backend::smt::{Satisfiability, SmtSolver, translates_exactly};
use k_rust_backend::substitution::Substitution;
use k_rust_backend::term::{Name, Sort, Symbol, Term, TermKind, Variable, VariableKind};
use k_rust_backend::unification::{UnificationResult, unify_term_pairs};

use crate::{
    execution::HaltClass,
    feasibility::{
        Inhabitation, LeafFeasibility, free_constructor, interpreted_predicate, proves_clash,
    },
    names::identifies_one_variable,
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
            sorts: definition.sorts.clone(),
            sort_graph: definition.sort_graph.clone(),
            symbols: definition
                .symbols
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
    /// Some rewrite rule has existential variables, so no variable name is stable on a path.
    pub existentials: bool,
    /// The signature projection compared between the sides.
    pub signature: SignatureProjection,
}

/// The facts of the default module of `backend`. A backend error is `Backend`.
pub fn definition_facts(backend: &mut Backend) -> Result<DefinitionFacts, NotProvedReason> {
    backend.with_solver(None, |definition, _| {
        Ok(DefinitionFacts {
            existentials: definition
                .rewrite_theory
                .values()
                .flat_map(|priorities| priorities.values())
                .flatten()
                .any(|rule| !rule.existentials.is_empty()),
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
/// domain values are kept; *stable* variables are kept; every other element variable whose
/// name identifies one variable (`identifies_one_variable`: the states are decoded from
/// k-rust's externalized KORE, whose variable names are not injective) is renamed apart
/// consistently within the scope; every other subterm (a variable with any other name, a
/// non-free application, a set variable, a collection, a conjunction) becomes a fresh wildcard
/// variable of its sort, one per occurrence. The stable variables are the free variables of
/// `initial` when neither side has existential rewrite variables and every one of them
/// internalizes to an element variable of an inhabited sort whose name identifies one
/// variable, and none otherwise. A leaf's predicate conjuncts (its `pc`, from the leaf state)
/// are kept apart and never generalized. A covering-side path `q` excludes a witness path `p`
/// by the first of: `Vacuous` (`q` halts Vacuous, or is Unsat and every variable name of its
/// leaf state identifies one variable), `Length` (on positions `states.len() - 1`: `q`
/// terminal and shorter, or `p` terminal and `q` longer), `Clash` (a clash that
/// `proves_clash` certifies in the joint unification of the generalized states at every
/// common position) and `Disjoint` (both pcs non-empty, a non-empty stable set, only stable
/// variables, only hooked, free-constructor, injection and domain-value symbols, an exact SMT
/// translation, and a solver `Unsat` for their conjunction). A side is covering when it has a
/// leaf and every leaf halts Stuck, Trivial, Vacuous, Indeterminate or DepthBound; a witness is
/// a leaf that is not Vacuous and is Syntactic or Solver feasible. With the mutant, then the
/// baseline, as the witness side and the other side covering, the first witness in leaf order
/// that every covering leaf excludes is `Proved`, with one exclusion per covering leaf in leaf
/// order. Otherwise the result is `NotCovering` when neither direction was attempted,
/// `Internalization` when a leaf failed to internalize, and `NoWitness` otherwise; a backend
/// error is `Backend`.
///
/// **Claim.** `Proved` means that some ground instance σ of `initial` has, as the two
/// definitions execute in k-rust, a witness-side state sequence that no covering-side sequence
/// equals.
///
/// **Proof.** Decoding is sound for the witness: its decoded states and pc are the real ones
/// under a merge μ of the variables that print alike (of one sort), so a θ satisfying the
/// decoded pc gives θ∘μ satisfying the real one. The witness `p` is feasible, so some θ
/// satisfies its pc; let σ be θ restricted to the variables of `initial`. k-rust keeps every
/// condition it relied on in the leaf predicate, so θ∘μ follows `p`: σ has a witness-side
/// sequence `S` whose states `0..=n_p` are instances of `p`'s states, ending there if `p` is
/// terminal. If the covering side had a σ-sequence
/// `S' = S`, then, because strategy `all` with PathSet leaves covers the initial state and the
/// covering condition excludes breadth bounds, cancellation and errors, `S'` follows some
/// covering path `q` under a θ' that agrees with σ on the initial variables. Each exclusion
/// contradicts `S' = S`. `Vacuous`: `q` has no instance (a merge can make a feasible pc Unsat,
/// so Unsat counts only when every name of the leaf state identifies one variable, and then
/// the decoded pc is the real one up to renaming). `Length`: a Stuck or Trivial leaf has
/// no defined successor, so the lengths differ. `Clash`: equal states at every common position
/// would be a common solution of the generalized equations (each wildcard or renamed variable
/// taking the value it hides, which holds because a consistently renamed name stands for one
/// variable and every other variable is renamed per occurrence; each stable variable its one
/// value along the path, because k-rust mints every new variable with a `!` counter or a
/// marker, and so never re-binds an initial name, and no other variable prints as a stable
/// name), and a certified clash has none in K's free-constructor algebra, which means the
/// same on both sides because the projections are equal. `Disjoint`: σ satisfies both pcs
/// because they mention only stable variables, their symbols mean the same in both
/// definitions, and the translation is exact, so the solver's `Unsat` contradicts σ. Every
/// covering path is excluded, so no covering-side sequence from σ equals `S`.
///
/// Positions count Rewrite transitions, so a Stuck and a Trivial leaf at the same state have
/// the same length: the certificate never separates a Stuck end from an undefined step
/// (EI-T05). Duplicate paths, leaf order and which rule fired are not evidence.
///
/// **Trust base.** k-rust's `all`-mode coverage, symbolic soundness and feasibility contracts
/// (every symbolic verdict trusts them); the unifier's clash soundness (`proves_clash`, as
/// `BackendRelations`); solver `Unsat` and the consistency of the baseline's smt-lemmas, which
/// a `Disjoint` query asserts. A mutant-side witness's feasibility is decided under that side's
/// supported lemmas only; on a patched ground run, lemmas the mutant inserted are trusted in
/// that side's normal forms, and a lemma headed by a constructor, which contradicts freeness, is
/// not seen by `Clash` (the state oracle has the same trust). A covering leaf's `Unsat` is
/// decided by the backend of the side that ran it, under that side's supported lemmas: a
/// `Vacuous` exclusion of a mutant-side leaf trusts the mutant's lemmas as that side's `Vacuous`
/// halts and its feasibility already do. The sequences' branch check relies on k-rust running
/// one request deterministically, and fails closed if it does not.
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
    let existentials = baseline_facts.existentials || mutant_facts.existentials;
    backend
        .with_solver(None, |definition, solver| {
            Ok::<_, NotProvedReason>(
                Prover::new(definition, solver, initial, existentials)
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
    fn new(
        definition: &'a BackendDefinition,
        solver: &'a dyn SmtSolver,
        initial: &Pattern,
        existentials: bool,
    ) -> Self {
        let stable = if existentials {
            BTreeSet::new()
        } else {
            let inhabitation = Inhabitation::of(definition);
            initial
                .free_variables()
                .into_iter()
                .map(|variable| {
                    match definition
                        .internalize_term(&Pattern::Variable(variable), &[])
                        .as_ref()
                        .map(Term::kind)
                    {
                        Ok(TermKind::Variable(internal))
                            if internal.kind == VariableKind::Element
                                && inhabitation.contains(&internal.sort)
                                && identifies_one_variable(&internal.name) =>
                        {
                            Some(internal.clone())
                        }
                        _ => None,
                    }
                })
                .collect::<Option<BTreeSet<_>>>()
                .unwrap_or_default()
        };
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
            let pattern = self.definition.internalize_pattern(state, &[]).ok()?;
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
        if q.halt == HaltClass::Vacuous
            || (q.feasibility == LeafFeasibility::Unsat
                && q.states.last().is_some_and(|state| {
                    state
                        .variables()
                        .iter()
                        .all(|variable| identifies_one_variable(&variable.name))
                }))
        {
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
                self.solver.is_sat(&query, &Substitution::new()),
                Ok(Satisfiability::Unsat)
            )
    }
}

/// The generalization scope of one state of one leaf of one side.
struct Scope<'a> {
    stable: &'a BTreeSet<Variable>,
    /// Unique per scope; contains `!`, so no generated name is a stable name.
    prefix: String,
    renamed: BTreeMap<Variable, Variable>,
    fresh: usize,
}

impl Scope<'_> {
    fn fresh(&mut self, sort: Sort) -> Variable {
        self.fresh += 1;
        Variable::new(format!("{}!{}", self.prefix, self.fresh), sort)
    }

    fn generalize(&mut self, term: &Term) -> Term {
        match term.kind() {
            TermKind::Variable(variable)
                if variable.kind == VariableKind::Element && self.stable.contains(variable) =>
            {
                term.clone()
            }
            TermKind::Variable(variable)
                if variable.kind == VariableKind::Element
                    && identifies_one_variable(&variable.name) =>
            {
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
