//! The join of a critical pair: both sides rewritten by steps that are `->E` steps on every
//! instance of the pair, until they reach one term or no step can be justified.
//!
//! A subterm of a side is *settled* when it is a normal form on every instance the pair speaks
//! about: a variable, a domain value, a constructor or injection term or a collection of settled
//! terms, a value the unifier gave a variable of either left-hand side (a subterm of an innermost
//! redex's normal-form arguments, or of an outer equation's valuation by elements), or an
//! equation-head application of settled arguments with which no executable equation offered at
//! its index, at a member of its overload family or at a bare variable unifies, except equations
//! whose `requires` is refuted at that unifier. A *residual* is an unsettled subterm on which the
//! join can take no step; its value on an instance is some normal form or `\bottom`.
//!
//! Each side is rewritten leftmost-innermost: the leftmost unsettled application whose proper
//! subterms are all settled or residual is tried, in this order:
//!
//! 1. a hooked application of domain values is evaluated by its hook (`\bottom` where the hook is
//!    undefined);
//! 2. the priority groups offered at its index are tried, highest first. An equation *surely
//!    applies* when the backend matcher, reading only the settled roots as values
//!    (`matching::match_with_settled_evidence`), matches it with every residual replaced by a
//!    placeholder variable, it has no `ensures`, its `requires` is absent or simplifies to `\top`
//!    with every claim withheld, and it binds every variable of its result. A group is *refuted*
//!    when every equation of it fails to unify with the subterm (residuals read as variables) or
//!    has its `requires` refuted at each unifier. The first group with an equation that surely
//!    applies gives the step; a group that is neither refuted nor gives a step leaves the subterm
//!    a residual;
//! 3. when every group is refuted (the witness group of the index included, in a pass with
//!    witness equations, `witness.rs`), a partial declared function without a hook is stuck on
//!    every instance and the subterm is `\bottom`, in `M_NF` and in `M+`, whose relation offers
//!    the witnesses as the lowest group of their index; an application of any other class but a
//!    hooked one (`symbols.rs`: an equation head, a total symbol, a partial symbol that is not a
//!    declared function) whose arguments are settled is settled (a stuck total application is an
//!    element no equation names).
//!
//! The binding rule keeps every step valid on every instance: the matcher compares only settled
//! structure, so each residual lies inside the value of some variable `X`, and the step is taken
//! only when `X` occurs in the equation's right-hand side, or its value is defined on every
//! instance (built from settled terms and applications of symbols declared total). Otherwise the
//! step is refused and the subterm is a residual: a step that erased an undefined residual would
//! identify a defined term with `\bottom`.
//!
//! Why "joined" is sound (the lifting lemma): the instances range over the signature with one
//! fresh constant in each sort that is not surely inhabited, and the steps are those of `R ∪ W`
//! (the executable equations and the pass's witness equations, `M+` in `confluence.rs`). On an
//! instance `rho` of the pair's variables at which both `requires` hold, each residual `R` has one
//! normal form `n_R` (it is a subterm of a reduct of the peak, below the peak in the well-founded
//! order of Newman's lemma, which A1+ gives). Replacing every residual instance by its normal
//! form, each join step is a step of that relation on the instance, or both its sides are
//! `\bottom` there (a residual that is `\bottom` occurs in the result by the binding rule, or the
//! step erases only a subterm defined on every instance). So both sides reach the common term's
//! instance, and the peak's two reducts have a common reduct. No rule reads emptiness, and one
//! reads coverage: the unifier enumerates subsort branches, and a complement case only assumes
//! that no offered left-hand side matches, so the argument holds with the constants as with any
//! element; a complement is dropped only for a sort whose every element in `M+`, the constants
//! included, is an application of one of its constructors (F2 at [`join`], which asks for a sort
//! that gets no constant and has no proper subsort, so none of a subsort's either).
//!
//! The join's precision is frozen at these rules. A rule that lets more pairs join (a step, a
//! settled shape or a refutation not stated above) keeps more claims, and a wrong one shows only
//! as a claim that holds in no model; so a new rule comes with a definition of the class it
//! decides in the axiom-instance harness (`tests/definedness_oracle/axioms.rs`), which judges the
//! claims by the axioms, and a defect switch in the rule (`switches.rs`) that the harness catches.
//! F1 and F2 (closing a case whose conditions are refuted under its substitution, and dropping a
//! complement its branches cover, at [`join`]) are such rules: their class is the oracle's
//! constructor-split templates (`generator::constructor_split`), judged by the harness and by
//! `D+`'s constants, and their switches are `close_case_without_refutation`,
//! `drop_complement_without_coverage` and `coverage_ignores_empty_subsorts`.
//! The witness equations add steps only through the groups the check offers; they are adopted
//! only after a second pass checks every pair with them, and their class is judged by the
//! oracle's `D+` with the verdict's witnesses. Open mode ([`Mode::Open`]), which reads a stuck
//! partial application at an element of a sort with no normal form as an atom, is no rule of the
//! verdict: it only proposes witnesses to that second pass, so a wrong proposal costs a join,
//! never a claim. Its atoms enter the case's settled terms like any normal form, so the rest of
//! that join reads them as normal forms too: a constructor pattern at an atom is refuted there
//! (`known_normal`), and a lower group such as an `owise` equation may then apply to a term
//! holding one. What it proposes is only a candidate: the well-formedness of each witness is
//! checked again (`witness.rs`) and the second pass decides.

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};

use k_rust_kore::measure::{self, Counter};

use super::{
    Conditions, Context, UnjoinedReason, children, replace_at, right_hand_side, subterm_at,
    symbols::Class,
};
use crate::{
    matching::{MatchResult, match_with_settled_evidence},
    rule::{RewriteRule, applicable_groups, rename_apart, term_index},
    simplify::{SimplificationOptions, simplify},
    substitution::{Substitution, compose, substitute},
    term::{
        FunctionType, HeadRole, SymbolType, Term, TermKind, Variable,
        head::NormalEvidence,
        names::{FreshMarker, with_fresh_marker},
    },
};

/// The most steps the join takes on one side.
pub(super) const JOIN_STEPS: usize = 32;

/// A side may grow to this many times the larger side's size before the join gives up.
const SIZE_FACTOR: usize = 4;

/// Witness that the join found an equation-head application settled; the only argument of
/// `NormalEvidence::settled`.
pub(crate) struct SettledRoot(());

#[cfg(test)]
impl SettledRoot {
    /// Test builds: the witness, for tests that state settledness from an independent oracle.
    pub(crate) fn for_tests() -> Self {
        Self(())
    }
}

/// How the join reads a stuck application of a declared partial function without a hook.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Mode {
    /// As `\bottom` (rule 3), and so the complement of a split on one: the verdict's reading.
    Verdict,
    /// As a settled *open atom* (entered among the case's settled terms, so read as a normal form
    /// by the rest of the join) when it holds a variable of a sort with no normal form
    /// (`Context::empty_sort`), and as `\bottom` otherwise: pass 1's proposal of witness
    /// equations (`witness.rs`) reads where the two sides differ around such atoms. No verdict
    /// is ever read from this mode.
    Open,
}

/// What the join found.
pub(super) enum Outcome {
    Joined,
    NotJoined {
        reached: (Option<Term>, Option<Term>),
        refused: Option<Term>,
        reason: UnjoinedReason,
        /// In [`Mode::Open`], the open atoms the failing case read as settled, in the order
        /// found; empty in [`Mode::Verdict`].
        open_atoms: Vec<Term>,
    },
}

struct Join<'c, 'd> {
    context: &'c mut Context<'d>,
    lifting: bool,
    mode: Mode,
    /// The free variables of the pair's conditions under `unifier ∘ theta` that occur in no left-
    /// hand side (`requires`-only variables), which a split's renaming apart must avoid too, so
    /// that F1 does not conflate them with an equation's variable (the others are in `values`).
    condition_only: BTreeSet<Variable>,
    /// The open atoms this case reads as settled ([`Mode::Open`]).
    open_atoms: Vec<Term>,
    /// Terms known settled.
    settled: FxHashSet<Term>,
    /// Applications this case assumes `\bottom`: stuck functions of a complement case.
    bottom: FxHashSet<Term>,
    /// Equation-head applications of settled arguments found not settled.
    unsettled: FxHashSet<Term>,
    residual: FxHashSet<Term>,
    /// The residuals in the order the join found them, each with the side it was found on.
    residuals: Vec<(Term, usize)>,
    /// The side being normalized, and the steps each side took.
    side: usize,
    steps: [usize; 2],
    refused: Option<Term>,
}

/// The most cases one pair's join explores.
pub(super) const JOIN_CASES: usize = 64;

/// The most nested case splits.
const SPLIT_DEPTH: usize = 6;

/// The conditions of the pair a join is about: its two equations, whose `requires` the join
/// re-reads under each case a split made (F1), at the overlap's unifier.
pub(super) struct PairConditions<'r> {
    pub(super) rules: [&'r RewriteRule; 2],
    pub(super) unifier: &'r Substitution,
}

/// One case of a pair: its sides, the values known settled in it, and the applications it
/// assumes normal (`settled`) or `\bottom`.
struct Case {
    sides: (Option<Term>, Option<Term>),
    /// The substitution the splits that made this case applied to the pair's sides, composed
    /// (empty for the pair itself and for a complement of it).
    theta: Substitution,
    /// Whether `theta` is new in this case (a branch of a split, not a complement), so that the
    /// pair's conditions say something new under it.
    reread: bool,
    values: Vec<Term>,
    settled: Vec<Term>,
    bottom: Vec<Term>,
    /// Of `settled`, the open atoms a complement case reads as settled ([`Mode::Open`]).
    open: Vec<Term>,
    depth: usize,
}

/// ```toml algorithm-site
/// id = "backend.confluence.critical_pairs"
/// role = "part"
/// sites = ["join", "Join::normalize", "Join::step", "Join::split"]
/// ```
///
/// Join the two sides of a pair; `values` are the values the unifier gave the variables of the
/// pair's left-hand sides, which are settled.
///
/// A case the join cannot close may be split on a residual `u` whose arguments are settled and
/// whose head is an equation head or a function without a hook: for each unifier `theta` of `u`
/// with the left-hand side of an equation that could rewrite it (its `requires` not refuted
/// there), the case instantiated by `theta`; and the complement case, in which `u` is a normal
/// form (an equation head) or `\bottom` (a stuck function). Every instance of the case is an
/// instance of some `theta` or is not: in the first case it is an instance of that branch, and in
/// the second no equation's left-hand side matches `u`'s instance (unification is complete),
/// whose arguments are normal forms, so it is a normal form or stuck. So the case is joined when
/// every branch is. The values of the case stay settled under `theta`: they are normal forms on
/// every instance, and so are their instances.
///
/// Two rules close a case without joining its sides, each because the case has no instance at
/// which both conditions hold, so no peak:
///
/// - **F1.** A branch whose pair's conditions, re-read under the unifier composed with the
///   case's substitution (`unifier ∘ theta`), are refuted (`Context::conditions`: they hold on
///   no instance in any model). The branch's instances are the pair's instances that are
///   instances of `theta`, and the conditions hold on none of them.
/// - **F2.** The complement of a split whose unifiers bind one variable `x` of the residual, and
///   only it, each to an application of a constructor, and bind it to `c(Y1, ..., Yn)`, with
///   distinct variables of `c`'s argument sorts that occur nowhere else in the case, for each
///   constructor `c` of `x`'s sort, when those constructors cover that sort
///   (`Sorts::constructors_covering`: every element of the sort in `M+` and in `M'` is one of
///   their applications). The case's instances read `x` as a normal form, which is then an
///   instance of some branch, so the complement has none. The pair is then counted as joined,
///   not refuted: "refuted" says the conditions hold on no instance in any model, and "joined"
///   ranges over the instances the lifting lemma speaks about, whose arguments are normal forms.
pub(super) fn join(
    context: &mut Context<'_>,
    lifting: bool,
    sides: (Option<Term>, Option<Term>),
    values: &[Term],
    mode: Mode,
    conditions: &PairConditions<'_>,
) -> Outcome {
    let cap = SIZE_FACTOR
        * sides
            .0
            .iter()
            .chain(sides.1.iter())
            .map(size)
            .max()
            .unwrap_or(1)
            .max(16);
    let mut cases = vec![Case {
        sides,
        theta: Substitution::new(),
        reread: false,
        values: values.to_vec(),
        settled: Vec::new(),
        bottom: Vec::new(),
        open: Vec::new(),
        depth: 0,
    }];
    let mut explored = 0;
    while let Some(case) = cases.pop() {
        explored += 1;
        if case.reread && closed_by_conditions(context, conditions, &case.theta) {
            continue;
        }
        let mut join = Join {
            condition_only: condition_only_variables(conditions, &case.theta),
            context: &mut *context,
            lifting,
            mode,
            open_atoms: case.open.clone(),
            settled: FxHashSet::default(),
            bottom: case.bottom.iter().cloned().collect(),
            unsettled: FxHashSet::default(),
            residual: FxHashSet::default(),
            residuals: Vec::new(),
            side: 0,
            steps: [0; 2],
            refused: None,
        };
        for value in case.values.iter().chain(&case.settled) {
            join.mark_settled(value);
        }
        if join.contradicts(&case.values) {
            // Some value is not a normal form on any instance: the case has no instance the
            // pair speaks about.
            continue;
        }
        let (left, left_exhausted) = join.normalize(case.sides.0.clone(), cap);
        join.side = 1;
        let (right, right_exhausted) = join.normalize(case.sides.1.clone(), cap);
        if left == right {
            continue;
        }
        if explored < JOIN_CASES
            && case.depth < SPLIT_DEPTH
            && !left_exhausted
            && !right_exhausted
            && let Some(branches) = join.split(&case, (&left, &right))
        {
            cases.extend(branches);
            continue;
        }
        let reason = if join.refused.is_some() {
            UnjoinedReason::JoinRefused
        } else if left_exhausted || right_exhausted || explored >= JOIN_CASES {
            UnjoinedReason::JoinBudget
        } else {
            UnjoinedReason::DifferentResults
        };
        return Outcome::NotJoined {
            reached: (left, right),
            refused: join.refused,
            reason,
            open_atoms: join.open_atoms,
        };
    }
    Outcome::Joined
}

/// F1: whether the pair's conditions, under `unifier ∘ theta`, hold on no instance, so that the
/// case of `theta` has no peak. Test switch `close_case_without_refutation`: also when they are
/// only not shown to hold.
fn closed_by_conditions(
    context: &mut Context<'_>,
    conditions: &PairConditions<'_>,
    theta: &Substitution,
) -> bool {
    match context.conditions(&conditions.rules, &compose(theta, conditions.unifier)) {
        Conditions::Refuted => true,
        Conditions::Holds => false,
        Conditions::Open(..) => super::switches::active().close_case_without_refutation,
    }
}

/// The free variables, under `unifier ∘ theta`, of the pair's `requires`-only variables (those
/// no left-hand side binds): usually none.
fn condition_only_variables(
    conditions: &PairConditions<'_>,
    theta: &Substitution,
) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    for rule in conditions.rules {
        for variable in &rule.computed_attributes.unbound_variables {
            let value = match conditions.unifier.get(variable) {
                Some(value) => substitute(value, theta),
                None => substitute(&Term::variable(variable.clone()), theta),
            };
            variables.extend(value.attributes().variables.iter().cloned());
        }
    }
    variables
}

/// Whether `symbol` is declared total (`functional` or `total`): its application to defined
/// arguments is defined (precondition P2).
/// Test switch `stuck_total_is_bottom`: revision 2's 3.13 (c), which read every function
/// application as never a normal form and a stuck one as `\bottom`.
fn stuck_total_is_bottom(symbol: &crate::term::Symbol) -> bool {
    super::switches::active().stuck_total_is_bottom
        && matches!(symbol.attributes.head_role(), HeadRole::Function { .. })
}

/// Every application subterm of `term`, `term` included.
fn collect_applications(term: &Term, into: &mut Vec<Term>) {
    if matches!(term.kind(), TermKind::Application { .. }) {
        into.push(term.clone());
    }
    for child in children(term) {
        collect_applications(&child, into);
    }
}

/// Whether `substitution` maps its variables injectively to variables.
fn renaming(substitution: &Substitution) -> bool {
    let mut targets = FxHashSet::default();
    substitution
        .values()
        .all(|value| matches!(value.kind(), TermKind::Variable(_)) && targets.insert(value.clone()))
}

fn size(term: &Term) -> usize {
    1 + children(term).iter().map(size).sum::<usize>()
}

/// One step's outcome.
enum Step {
    /// The subterm rewrites to this (`None`: `\bottom`).
    To(Option<Term>),
    Settled,
    Residual,
}

impl Join<'_, '_> {
    /// Record `term` and its subterms as settled: a subterm of a normal form is a normal form.
    fn mark_settled(&mut self, term: &Term) {
        if self.settled.insert(term.clone()) {
            for child in children(term) {
                self.mark_settled(&child);
            }
        }
    }

    fn known_settled(&self, term: &Term) -> bool {
        self.settled.contains(term)
    }

    /// Rewrite `side` until no step is found; `true` when the step or size budget ran out.
    fn normalize(&mut self, side: Option<Term>, cap: usize) -> (Option<Term>, bool) {
        let Some(mut term) = side else {
            return (None, false);
        };
        let mut steps = 0;
        loop {
            let Some(path) = self.find_redex(&term, &mut Vec::new()) else {
                return (Some(term), false);
            };
            let redex = subterm_at(&term, &path);
            if self.bottom.contains(&redex) {
                return (None, false);
            }
            match self.step(&redex) {
                Step::To(None) => return (None, false),
                Step::To(Some(result)) => {
                    term = replace_at(&term, &path, result);
                    steps += 1;
                    self.steps[self.side] += 1;
                    self.context.counts.join_steps += 1;
                    measure::bump(Counter::ConfluenceJoinSteps);
                    if steps >= JOIN_STEPS || size(&term) > cap {
                        return (Some(term), true);
                    }
                }
                Step::Settled => self.mark_settled(&redex),
                Step::Residual if super::switches::active().decompose_refused_redex => {
                    self.mark_settled(&redex);
                }
                Step::Residual => {
                    if self.residual.insert(redex.clone()) {
                        self.residuals.push((redex, self.side));
                    }
                }
            }
        }
    }

    /// The position of the leftmost unsettled application whose proper subterms are all settled
    /// or residual, if any.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn find_redex(&mut self, term: &Term, path: &mut Vec<usize>) -> Option<Vec<usize>> {
        if self.known_settled(term) || self.residual.contains(term) {
            return None;
        }
        for (index, child) in children(term).iter().enumerate() {
            path.push(index);
            let found = self.find_redex(child, path);
            path.pop();
            if found.is_some() {
                return found;
            }
        }
        match term.kind() {
            TermKind::Application { symbol, .. } => match symbol.attributes.head_role() {
                HeadRole::FreeConstructor => None,
                HeadRole::EquationHead => (!self.settled_application(term)).then(|| path.clone()),
                HeadRole::Function { .. } | HeadRole::Residual | HeadRole::Uninterpreted => {
                    Some(path.clone())
                }
            },
            TermKind::Variable(_)
            | TermKind::DomainValue { .. }
            | TermKind::Injection { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. }
            | TermKind::And(..) => None,
        }
    }

    /// Whether `term` is settled, deciding equation-head applications on the way.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn is_settled(&mut self, term: &Term) -> bool {
        if self.known_settled(term) {
            return true;
        }
        match term.kind() {
            TermKind::Variable(_) | TermKind::DomainValue { .. } => true,
            TermKind::Injection { term, .. } => self.is_settled(term),
            TermKind::Map { .. } | TermKind::List { .. } | TermKind::Set { .. } => {
                children(term).iter().all(|child| self.is_settled(child))
            }
            TermKind::And(..) => false,
            TermKind::Application {
                symbol, arguments, ..
            } => match symbol.attributes.head_role() {
                HeadRole::FreeConstructor => {
                    arguments.iter().all(|argument| self.is_settled(argument))
                }
                HeadRole::EquationHead => self.settled_application(term),
                HeadRole::Function { .. } | HeadRole::Residual | HeadRole::Uninterpreted => false,
            },
        }
    }

    /// Whether an equation-head application is settled: its arguments are, and no executable
    /// equation that could rewrite it unifies with it (except where its `requires` is refuted).
    fn settled_application(&mut self, application: &Term) -> bool {
        if self.known_settled(application) {
            return true;
        }
        if self.unsettled.contains(application) {
            return false;
        }
        let arguments_settled = children(application)
            .iter()
            .all(|argument| self.is_settled(argument));
        let settled = arguments_settled
            && self
                .context
                .offered(&term_index(application))
                .iter()
                .all(|rule| self.refuted_at(rule, application));
        if settled {
            self.mark_settled(application);
        } else {
            self.unsettled.insert(application.clone());
        }
        settled
    }

    /// Whether no instance of `subject` (its variables read as normal forms) is an instance of
    /// `rule`'s left-hand side at which its `requires` may hold.
    fn refuted_at(&mut self, rule: &RewriteRule, subject: &Term) -> bool {
        let renamed =
            rename_apart(rule, &subject.attributes().variables, &[]).map(|(renamed, _)| renamed);
        let rule = renamed.as_ref().unwrap_or(rule);
        let settled = &self.settled;
        let known_normal = |term: &Term| settled.contains(term);
        // With deferral: a relaxed solution covers every instance it stands for, so refuting the
        // `requires` at each solution refutes it at every unifier (`unify.rs`).
        let unifiers =
            match self
                .context
                .unify_relaxed(self.lifting, &known_normal, subject, &rule.lhs)
            {
                Ok(unifiers) => unifiers,
                Err(_) => return false,
            };
        unifiers.iter().all(|(unifier, deferred)| {
            (deferred.is_some() && super::switches::active().defer_without_refutation)
                || self.context.refuted(&[rule], unifier)
        })
    }

    /// One step at `redex`, whose proper subterms are settled or residual.
    fn step(&mut self, redex: &Term) -> Step {
        let TermKind::Application {
            symbol, arguments, ..
        } = redex.kind()
        else {
            return Step::Residual;
        };
        if symbol.attributes.hook.is_some()
            && arguments
                .iter()
                .all(|argument| matches!(argument.kind(), TermKind::DomainValue { .. }))
        {
            return self.hook(redex);
        }
        // Residual subterms are read through placeholders: the matcher binds a placeholder only
        // to a variable of the pattern, so the step decomposes only settled structure.
        let mut placeholders = FxHashMap::<Term, Variable>::default();
        let subject = self.placeheld(redex, true, &mut placeholders);
        let restore = placeholders
            .iter()
            .map(|(residual, placeholder)| (placeholder.clone(), residual.clone()))
            .collect::<Substitution>();
        let groups = applicable_groups(&self.context.groups, &term_index(redex));
        for rules in groups.values() {
            let mut refuted = true;
            for rule in rules {
                if let Some(result) = self.surely_applies(rule, &subject, &restore) {
                    return result;
                }
                if !self.refuted_at(rule, &subject) {
                    refuted = false;
                }
            }
            if !refuted && !super::switches::active().ignore_higher_groups {
                return Step::Residual;
            }
        }
        // Every group is refuted: no equation rewrites any instance at its root.
        let arguments_settled = arguments.iter().all(|argument| self.is_settled(argument));
        // `->E` rule 3 (`symbols.rs`): a stuck application of a declared partial function is
        // `\bottom`; of every other class but a hooked one, a normal form (for a total symbol,
        // an element no equation names, as precondition P2 requires).
        match Class::of(symbol) {
            Class::PartialFunction
                if self.mode == Mode::Open
                    && arguments_settled
                    && self.context.holds_empty_variable(redex) =>
            {
                self.open_atom(redex);
                Step::Settled
            }
            Class::PartialFunction => Step::To(None),
            Class::Total { .. } if stuck_total_is_bottom(symbol) => Step::To(None),
            Class::EquationHead | Class::Total { .. } | Class::OtherPartial
                if arguments_settled =>
            {
                Step::Settled
            }
            Class::Constructor
            | Class::Collection
            | Class::EquationHead
            | Class::Hooked { .. }
            | Class::Total { .. }
            | Class::OtherPartial => Step::Residual,
        }
    }

    /// Record `atom`, an application of a declared partial function without a hook that holds a
    /// variable of a sort with no normal form, as an open atom of this case ([`Mode::Open`]).
    fn open_atom(&mut self, atom: &Term) {
        if !self.open_atoms.contains(atom) {
            self.open_atoms.push(atom.clone());
        }
    }

    /// `term` with each maximal residual proper subterm replaced by a placeholder variable (one
    /// per residual).
    fn placeheld(
        &mut self,
        term: &Term,
        root: bool,
        placeholders: &mut FxHashMap<Term, Variable>,
    ) -> Term {
        if !root && self.residual.contains(term) {
            if let Some(placeholder) = placeholders.get(term) {
                return Term::variable(placeholder.clone());
            }
            let placeholder = Variable::new(
                with_fresh_marker("VarResidual", FreshMarker::Unify, self.context.fresh),
                term.sort(),
            );
            self.context.fresh += 1;
            placeholders.insert(term.clone(), placeholder.clone());
            return Term::variable(placeholder);
        }
        let new = children(term)
            .iter()
            .map(|child| self.placeheld(child, false, placeholders))
            .collect::<Vec<_>>();
        if new.is_empty() {
            return term.clone();
        }
        super::with_children(term, new)
    }

    /// The step `rule` takes on `subject` when it surely applies, after the binding rule; `None`
    /// when it does not surely apply. `restore` maps placeholders back to the residuals.
    fn surely_applies(
        &mut self,
        rule: &RewriteRule,
        subject: &Term,
        restore: &Substitution,
    ) -> Option<Step> {
        if !rule.ensures.is_empty() || !rule.computed_attributes.unbound_result_variables.is_empty()
        {
            return None;
        }
        let renamed =
            rename_apart(rule, &subject.attributes().variables, &[]).map(|(renamed, _)| renamed);
        let rule = renamed.as_ref().unwrap_or(rule);
        let settled = &self.settled;
        let evidence = |application: &Term| {
            settled
                .contains(application)
                .then(|| NormalEvidence::settled(SettledRoot(())))
        };
        let MatchResult::Success(matched) =
            match_with_settled_evidence(self.context.definition, &rule.lhs, subject, &evidence)
        else {
            return None;
        };
        let substitution = matched
            .iter()
            .map(|(variable, value)| (variable.clone(), substitute(value, restore)))
            .collect::<Substitution>();
        if !rule.requires.is_empty() {
            let instance = rule.requires.instantiate(&substitution);
            let definition = self.context.definition;
            let (predicates, stops) =
                super::budgeted(|| instance.with_definedness(definition, &[]));
            self.context.count_stops(stops);
            if stops.any() {
                return None;
            }
            let predicates = predicates.ok()?;
            if !matches!(
                self.context
                    .simplify(crate::rule::Predicate::And(predicates.into())),
                Some(crate::rule::Predicate::True)
            ) {
                return None;
            }
        }
        let Ok(result) = right_hand_side(rule) else {
            return None;
        };
        // The binding rule.
        let result_variables = result
            .as_ref()
            .map(|result| result.attributes().variables.clone())
            .unwrap_or_default();
        for (variable, value) in &matched {
            let holds_residual = value
                .attributes()
                .variables
                .iter()
                .any(|variable| restore.contains_key(variable));
            if holds_residual
                && !result_variables.contains(variable)
                && !self.defined_everywhere(&substitution[variable])
                && !super::switches::active().erase_partial_residuals
            {
                self.refused = Some(subject.clone());
                return Some(Step::Residual);
            }
        }
        Some(Step::To(
            result.map(|result| substitute(&result, &substitution)),
        ))
    }

    /// Whether `term` is defined on every instance: built from settled terms and applications
    /// of symbols declared total (precondition P2).
    fn defined_everywhere(&mut self, term: &Term) -> bool {
        if self.is_settled(term) {
            return true;
        }
        match term.kind() {
            TermKind::Application {
                symbol, arguments, ..
            } => {
                let total = symbol.attributes.head_role() == HeadRole::FreeConstructor
                    || symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Total);
                total
                    && arguments
                        .iter()
                        .all(|argument| self.defined_everywhere(argument))
            }
            TermKind::Injection { term, .. } => self.defined_everywhere(term),
            TermKind::Variable(_)
            | TermKind::DomainValue { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. }
            | TermKind::And(..) => false,
        }
    }

    /// Whether some value, which the case reads as a normal form, has a subterm that is not a
    /// normal form on any instance: an application of a symbol whose application to normal forms
    /// is never one (a declared partial function, `symbols.rs`), or an equation-head application
    /// to which some equation surely applies. A total function's stuck application is a normal
    /// form, so it decides nothing here.
    fn contradicts(&mut self, values: &[Term]) -> bool {
        let mut subterms = Vec::new();
        for value in values {
            collect_applications(value, &mut subterms);
        }
        for subterm in subterms {
            let TermKind::Application { symbol, .. } = subterm.kind() else {
                continue;
            };
            if Class::of(symbol).never_normal() || stuck_total_is_bottom(symbol) {
                return true;
            }
            match symbol.attributes.head_role() {
                HeadRole::Function { .. } => {}
                HeadRole::EquationHead => {
                    let groups = applicable_groups(&self.context.groups, &term_index(&subterm));
                    for rule in groups.values().flatten() {
                        if let Some(Step::To(_)) =
                            self.surely_applies(rule, &subterm, &Substitution::new())
                        {
                            return true;
                        }
                    }
                }
                HeadRole::FreeConstructor | HeadRole::Residual | HeadRole::Uninterpreted => {}
            }
        }
        false
    }

    /// The branches of `case` split on a residual that can be split, or `None`: the split with the
    /// fewest branches. Among equals, the residuals of the side that took fewer steps come first
    /// (it is the side that stopped short), and among them one that occurs in one reached side
    /// and not in the other (a residual both sides reached does not keep them apart), each in the
    /// order the join met them.
    fn split(&mut self, case: &Case, reached: (&Option<Term>, &Option<Term>)) -> Option<Vec<Case>> {
        let subterms = |side: &Option<Term>| {
            let mut all = Vec::new();
            if let Some(side) = side {
                collect_applications(side, &mut all);
            }
            all.into_iter().collect::<FxHashSet<_>>()
        };
        let (left, right) = (subterms(reached.0), subterms(reached.1));
        let behind = usize::from(self.steps[1] < self.steps[0]);
        let mut ordered = self.residuals.clone();
        ordered.sort_by_key(|(residual, side)| {
            (
                *side != behind,
                left.contains(residual) == right.contains(residual),
            )
        });
        // The split with the fewest branches, the first in this order among equals.
        let mut best = None;
        for (residual, _) in ordered {
            if self.refused.as_ref() == Some(&residual) {
                continue;
            }
            let TermKind::Application {
                symbol, arguments, ..
            } = residual.kind()
            else {
                continue;
            };
            let splittable = match symbol.attributes.head_role() {
                HeadRole::EquationHead => true,
                HeadRole::Function { .. } => symbol.attributes.hook.is_none(),
                HeadRole::FreeConstructor | HeadRole::Residual | HeadRole::Uninterpreted => false,
            };
            if !splittable || !arguments.iter().all(|argument| self.is_settled(argument)) {
                continue;
            }
            if let Some(branches) = self.split_on(case, &residual, symbol.attributes.head_role())
                && best
                    .as_ref()
                    .is_none_or(|best: &Vec<Case>| branches.len() < best.len())
            {
                best = Some(branches);
            }
        }
        best
    }

    fn split_on(&mut self, case: &Case, residual: &Term, role: HeadRole) -> Option<Vec<Case>> {
        let variables = residual.attributes().variables.clone();
        // The unifiers are applied to the whole case, so the equation's variables are named
        // apart from every variable of the case.
        let mut scope = variables.to_btree_set();
        scope.extend(self.condition_only.iter().cloned());
        for term in [&case.sides.0, &case.sides.1]
            .into_iter()
            .flatten()
            .chain(&case.values)
            .chain(&case.settled)
            .chain(&case.bottom)
        {
            scope.extend(term.attributes().variables.iter().cloned());
        }
        let mut instances = Vec::<Substitution>::new();
        for rule in self.context.offered(&term_index(residual)) {
            let renamed = rename_apart(&rule, &scope, &[]).map(|(renamed, _)| renamed);
            let rule = renamed.as_ref().unwrap_or(&rule);
            let settled = &self.settled;
            let known_normal = |term: &Term| settled.contains(term);
            let unifiers = self
                .context
                .unify(self.lifting, &known_normal, residual, &rule.lhs)
                .ok()?;
            for unifier in unifiers {
                if self.context.refuted(&[rule], &unifier) {
                    continue;
                }
                let restricted = unifier
                    .into_iter()
                    .filter(|(variable, _)| variables.contains(variable))
                    .collect::<Substitution>();
                if renaming(&restricted) {
                    // The unifier constrains no variable of the residual: the equation's
                    // left-hand side matches it on every instance, so no split separates it.
                    return None;
                }
                if !instances.contains(&restricted) {
                    instances.push(restricted);
                }
            }
        }
        let instantiate = |term: &Option<Term>, theta: &Substitution| {
            term.as_ref().map(|term| substitute(term, theta))
        };
        let mut branches = instances
            .iter()
            .map(|theta| Case {
                sides: (
                    instantiate(&case.sides.0, theta),
                    instantiate(&case.sides.1, theta),
                ),
                theta: compose(theta, &case.theta),
                reread: true,
                values: case
                    .values
                    .iter()
                    .map(|value| substitute(value, theta))
                    .collect(),
                settled: case
                    .settled
                    .iter()
                    .map(|term| substitute(term, theta))
                    .collect(),
                bottom: case
                    .bottom
                    .iter()
                    .map(|term| substitute(term, theta))
                    .collect(),
                open: case
                    .open
                    .iter()
                    .map(|term| substitute(term, theta))
                    .collect(),
                depth: case.depth + 1,
            })
            .collect::<Vec<_>>();
        if self.covers(&instances, &scope) {
            // F2: every instance of the case is an instance of some branch.
            return Some(branches);
        }
        let mut complement = Case {
            sides: case.sides.clone(),
            theta: case.theta.clone(),
            reread: false,
            values: case.values.clone(),
            settled: case.settled.clone(),
            bottom: case.bottom.clone(),
            open: case.open.clone(),
            depth: case.depth + 1,
        };
        let TermKind::Application { symbol, .. } = residual.kind() else {
            unreachable!("a split residual is an application")
        };
        if role == HeadRole::EquationHead
            || !(Class::of(symbol).stuck_is_bottom() || stuck_total_is_bottom(symbol))
        {
            complement.settled.push(residual.clone());
        } else if self.mode == Mode::Open
            && Class::of(symbol) == Class::PartialFunction
            && self.context.holds_empty_variable(residual)
        {
            // Open mode: the stuck partial application is an open atom of the complement.
            complement.settled.push(residual.clone());
            complement.open.push(residual.clone());
        } else {
            complement.bottom.push(residual.clone());
        }
        branches.push(complement);
        Some(branches)
    }

    /// F2: whether the split's unifiers `instances` (each restricted to the residual's
    /// variables) bind one variable `x`, and only it, each to a constructor application, and
    /// bind it to `c(Y1, ..., Yn)` for every constructor `c` of a sort its constructors cover
    /// (`Sorts::constructors_covering`), with `Y1, ..., Yn` distinct variables of `c`'s argument
    /// sorts outside `scope`, the case's variables. Test switch
    /// `drop_complement_without_coverage`: without the last condition.
    fn covers(&self, instances: &[Substitution], scope: &BTreeSet<Variable>) -> bool {
        let mut bound: Option<&Variable> = None;
        let mut general = FxHashSet::default();
        for theta in instances {
            let mut entries = theta.iter();
            let (Some((variable, value)), None) = (entries.next(), entries.next()) else {
                return false;
            };
            if *bound.get_or_insert(variable) != variable {
                return false;
            }
            let TermKind::Application {
                symbol, arguments, ..
            } = value.kind()
            else {
                return false;
            };
            if Class::of(symbol) != Class::Constructor {
                return false;
            }
            let mut fresh = FxHashSet::default();
            if arguments.len() == symbol.argument_sorts.len()
                && arguments
                    .iter()
                    .zip(&symbol.argument_sorts)
                    .all(|(argument, sort)| {
                        matches!(argument.kind(), TermKind::Variable(argument)
                        if argument.sort == *sort
                            && !scope.contains(argument)
                            && fresh.insert(argument.clone()))
                    })
            {
                general.insert(symbol.name.clone());
            }
        }
        let Some(variable) = bound else {
            return false;
        };
        super::switches::active().drop_complement_without_coverage
            || self
                .context
                .sorts
                .constructors_covering(&variable.sort)
                .is_some_and(|constructors| {
                    constructors
                        .iter()
                        .all(|constructor| general.contains(constructor))
                })
    }

    /// Evaluate a hooked application of domain values with the simplifier, under the check's
    /// budget of polls (`budgeted`): a hooked symbol whose hook this backend does not implement is
    /// evaluated by its equations, which need not end, nor stay within the stack. An evaluation
    /// that met a stop is a residual: it refuses the step, which can only lose a join.
    fn hook(&mut self, redex: &Term) -> Step {
        let definition = self.context.definition;
        let (simplified, stops) = super::budgeted(|| {
            simplify(
                definition,
                redex,
                SimplificationOptions {
                    max_iterations: super::CONDITION_ITERATIONS,
                    ..SimplificationOptions::default()
                },
            )
        });
        self.context.count_stops(stops);
        if stops.any() {
            if let Err(stop) = simplified {
                let _ = stop.into_cause();
            }
            return Step::Residual;
        }
        match simplified {
            Ok(Ok(simplified)) => {
                if !simplified.effects.is_empty() || simplified.exhausted.is_some() {
                    return Step::Residual;
                }
                if simplified
                    .conjoined()
                    .any(|predicate| *predicate == crate::rule::Predicate::False)
                    || simplified.undefined_term.is_some()
                {
                    return Step::To(None);
                }
                if simplified
                    .conjoined()
                    .all(|predicate| *predicate == crate::rule::Predicate::True)
                    && matches!(simplified.term.kind(), TermKind::DomainValue { .. })
                {
                    Step::To(Some(simplified.term))
                } else {
                    Step::Residual
                }
            }
            Ok(Err(_)) => Step::Residual,
            Err(stop) => {
                let _ = stop.into_cause();
                Step::Residual
            }
        }
    }
}
