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
//! 3. when every group is refuted, a partial declared function without a hook is stuck on every
//!    instance and the subterm is `\bottom`; an application of any other class but a hooked one
//!    (`symbols.rs`: an equation head, a total symbol, a partial symbol that is not a declared
//!    function) whose arguments are settled is settled (a stuck total application is an element
//!    no equation names).
//!
//! The binding rule keeps every step valid on every instance: the matcher compares only settled
//! structure, so each residual lies inside the value of some variable `X`, and the step is taken
//! only when `X` occurs in the equation's right-hand side, or its value is defined on every
//! instance (built from settled terms and applications of symbols declared total). Otherwise the
//! step is refused and the subterm is a residual: a step that erased an undefined residual would
//! identify a defined term with `\bottom`.
//!
//! Why "joined" is sound (the lifting lemma): on an instance `rho` of the pair's variables at
//! which both `requires` hold, each residual `R` has one normal form `n_R` (it is a subterm of a
//! reduct of the peak, below the peak in the well-founded order of Newman's lemma). Replacing
//! every residual instance by its normal form, each join step is an `->E` step on the instance,
//! or both its sides are `\bottom` there (a residual that is `\bottom` occurs in the result by the
//! binding rule, or the step erases only a subterm defined on every instance). So both sides
//! reach the common term's instance, and the peak's two reducts have a common reduct.
//!
//! The join's precision is frozen at these rules. A rule that lets more pairs join (a step, a
//! settled shape or a refutation not stated above) keeps more claims, and a wrong one shows only
//! as a claim that holds in no model; so a new rule comes with a definition of the class it
//! decides in the axiom-instance harness (`tests/definedness_oracle/axioms.rs`), which judges the
//! claims by the axioms, and a defect switch in the rule (`switches.rs`) that the harness catches.

use rustc_hash::{FxHashMap, FxHashSet};

use k_rust_kore::measure::{self, Counter};

use super::{
    Context, UnjoinedReason, children, replace_at, right_hand_side, subterm_at, symbols::Class,
};
use crate::{
    matching::{MatchResult, match_with_settled_evidence},
    rule::{RewriteRule, applicable_groups, rename_apart, term_index},
    simplify::{SimplificationOptions, simplify},
    substitution::{Substitution, substitute},
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

/// What the join found.
pub(super) enum Outcome {
    Joined,
    NotJoined {
        reached: (Option<Term>, Option<Term>),
        refused: Option<Term>,
        reason: UnjoinedReason,
    },
}

struct Join<'c, 'd> {
    context: &'c mut Context<'d>,
    lifting: bool,
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

/// One case of a pair: its sides, the values known settled in it, and the applications it
/// assumes normal (`settled`) or `\bottom`.
struct Case {
    sides: (Option<Term>, Option<Term>),
    values: Vec<Term>,
    settled: Vec<Term>,
    bottom: Vec<Term>,
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
pub(super) fn join(
    context: &mut Context<'_>,
    lifting: bool,
    sides: (Option<Term>, Option<Term>),
    values: &[Term],
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
        values: values.to_vec(),
        settled: Vec::new(),
        bottom: Vec::new(),
        depth: 0,
    }];
    let mut explored = 0;
    while let Some(case) = cases.pop() {
        explored += 1;
        let mut join = Join {
            context: &mut *context,
            lifting,
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
        };
    }
    Outcome::Joined
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
        let unifiers = match self
            .context
            .unify(self.lifting, &known_normal, subject, &rule.lhs)
        {
            Ok(unifiers) => unifiers,
            Err(_) => return false,
        };
        unifiers
            .iter()
            .all(|unifier| self.context.refuted(&[rule], unifier))
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
            let predicates = rule
                .requires
                .instantiate(&substitution)
                .with_definedness(self.context.definition, &[]);
            if !matches!(
                self.context
                    .simplify(crate::rule::Predicate::And(predicates)),
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
                depth: case.depth + 1,
            })
            .collect::<Vec<_>>();
        let mut complement = Case {
            sides: case.sides.clone(),
            values: case.values.clone(),
            settled: case.settled.clone(),
            bottom: case.bottom.clone(),
            depth: case.depth + 1,
        };
        let TermKind::Application { symbol, .. } = residual.kind() else {
            unreachable!("a split residual is an application")
        };
        if role == HeadRole::EquationHead
            || !(Class::of(symbol).stuck_is_bottom() || stuck_total_is_bottom(symbol))
        {
            complement.settled.push(residual.clone());
        } else {
            complement.bottom.push(residual.clone());
        }
        branches.push(complement);
        Some(branches)
    }

    /// Evaluate a hooked application of domain values with the simplifier.
    fn hook(&mut self, redex: &Term) -> Step {
        match simplify(
            self.context.definition,
            redex,
            SimplificationOptions {
                max_iterations: super::CONDITION_ITERATIONS,
                ..SimplificationOptions::default()
            },
        ) {
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
