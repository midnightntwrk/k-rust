//! Unification of two left-hand-side patterns over normal-form instances, modulo injection
//! composition and the overload axioms of confluent overload families.
//!
//! The problem: two patterns `s` and `t` (variables of the two sides named apart) have a common
//! instance when some valuation of their variables by normal forms makes `s sigma` and
//! `t sigma` equal modulo the matching theory `Th` (`value-contract`'s reading of the
//! evaluator's matcher): injection composition, `inj{B,A}(inj{C,B}(x)) = inj{C,A}(x)`, which
//! `Term::injection` applies on construction, and the overload axioms
//! `g(inj(x1), ..., inj(xn)) = inj(h(x1, ..., xn))` of a greater production `g` over a lesser `h`.
//!
//! The algorithm is Martelli and Montanari's: a list of equations between terms, each replaced by
//! equations between subterms that have the same solutions, or solved by binding a variable
//! (with an occurs check), or found to have no solution (a clash). Bindings are applied
//! eagerly to the remaining equations and to earlier bindings, so every substitution returned is
//! idempotent. Where one equation has several families of solutions the problem splits into
//! branches, explored depth first:
//!
//! - two injections into one sort from incomparable sorts `A` and `B` denote one value only
//!   through a value of a common subsort; every common subsort is below a maximal one, so one
//!   branch per maximal common subsort `C` covers them (order-sorted unification over a finite
//!   sort order is finitary);
//! - a greater overload application `g(p)` against an injection `inj{S,G}(z)` of a variable
//!   denotes one value only when `g(p sigma)` lowers to an injection of a lesser production; one
//!   branch per lesser production `h` of `g` whose result sort is below `S` binds `z` to an
//!   application of `h` to fresh variables and compares `g(p)` with its lift.
//!
//! Lifting (comparing `inj(h(q))` with `g(p)` through `g(inj(q))`) is an equivalence modulo
//! `Th` only in a family whose overload equations give every term one lowest form, which
//! stage 1 of the check establishes (`confluence.rs`); a comparison that needs lifting in a
//! family that is not known confluent answers [`UnresolvedShape::Family`]. A greater
//! application known to be a normal form (a value the caller knows normal, [`Unifier`]'s
//! `known_normal`) is in lowest form, so it is never an injection of a lesser production: it
//! clashes with one instead of branching.
//!
//! Two maps of one definition are compared over the instances at which both are defined: a
//! defined map term's explicit keys are pairwise distinct and none is a key of its rest
//! (`term.rs`), and a normal form is defined. Two facts then decide a map equation
//! (`Unifier::maps`). A map binds a key once, so two maps that bind one key term (written alike
//! on both sides, after the problem's bindings) are equal exactly when they give it one value
//! and are equal without it. And `n` explicit entries are `n` distinct keys, exactly `n` without
//! a rest, while a rest only adds keys, so a side without a rest and with fewer entries than the
//! other has no common instance with it. What is left after the shared keys is a rest against a
//! rest (an absent rest read as the empty map), a variable rest of a side with no entry left
//! (bound to the other side, entries and rest), or entries whose keys are not written alike,
//! which wait for the other equations' bindings and answer [`UnresolvedShape::Collection`] when
//! no binding comes (as does an opaque rest of a side with no entry left). A returned unifier
//! may have instances at which a map repeats a key; both sides are then `\bottom`, which is no
//! instance. An empty answer proves that the two have no common defined instance, which
//! `classify`, `Join::refuted_at` and `Join::split_on` all read. Sets are not decomposed.
//!
//! Every rule replaces an equation by equations with the same solutions over normal forms modulo
//! `Th`, so each returned substitution is a unifier (soundness), and every common instance is an
//! instance of one returned substitution (completeness), except where the answer is
//! [`UnresolvedShape`]: a shape the unifier does not decide completely, for which the caller
//! assumes nothing.

use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::{
    definition::BackendDefinition,
    matching::lift_to_overload,
    substitution::{Substitution, substitute},
    term::{
        HeadRole, Items, ListDefinition, Name, Sort, SortNode, Symbol, Term, TermKind, Variable,
        VariableKind,
        names::{FreshMarker, with_fresh_marker},
    },
};

/// The most branch states one unification explores before it answers
/// [`UnresolvedShape::Budget`]. A bound on work only: past it, the answer is the conservative one.
pub(crate) const UNIFIER_BRANCHES: usize = 4096;

/// A shape the unifier does not decide completely. The pair it occurs in is not joined.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum UnresolvedShape {
    /// Two collections outside the shapes decided completely (a collection pattern against a
    /// collection variable, two lists with fixed elements at the same end and one rest each, and
    /// two maps decided by their sizes, their keys written alike and their rests): two maps
    /// with no key written alike and no size clash (or a side left with no entry and an opaque
    /// rest), two sets, or lists with elements at both ends.
    Collection,
    /// A set variable.
    SetVariable,
    /// An application of a declared function, a macro or alias, or an uninterpreted symbol (its
    /// name) where a value is compared: its value is whatever its equations make it.
    Function(Name),
    /// A sort variable the comparison needs resolved.
    SortVariable,
    /// A comparison that needs the overload axioms of a family (one of its members) that is not
    /// known confluent, or that has no unique least common overload.
    Family(Name),
    /// More than `UNIFIER_BRANCHES` branch states.
    Budget,
    /// A left-hand side that matches one subject in several ways (a map or set pattern with an
    /// entry the rest of the left-hand side does not fix), whose right-hand side or `ensures`
    /// reads a variable the choice of matching decides: the equation with itself is a peak.
    SeveralMatches,
}

impl std::fmt::Display for UnresolvedShape {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Collection => formatter.write_str(
                "two collections the unifier does not decide (two maps with no key written alike and no size clash, two sets, or lists with elements at both ends)",
            ),
            Self::SetVariable => formatter.write_str("a set variable"),
            Self::Function(symbol) => write!(
                formatter,
                "an application of `{symbol}`, whose value its equations decide, where a value is compared"
            ),
            Self::SortVariable => formatter.write_str("a sort variable the comparison needs resolved"),
            Self::Family(symbol) => write!(
                formatter,
                "a comparison through the overload family of `{symbol}`, which is not known confluent"
            ),
            Self::Budget => formatter.write_str("more unifier branches than the check explores"),
            Self::SeveralMatches => formatter.write_str(
                "a map or set pattern that matches one collection in several ways, with a result that depends on the choice",
            ),
        }
    }
}

/// The overload families of a definition: the connected components of its `symbol-overload`
/// relation, and which of them are known confluent (stage 1, `confluence.rs`).
#[derive(Clone, Debug, Default)]
pub(crate) struct Families {
    family_of: FxHashMap<Name, usize>,
    members: Vec<Vec<Name>>,
    confluent: Vec<bool>,
}

impl Families {
    /// The families of `definition`, none of them yet known confluent.
    pub(crate) fn of(definition: &BackendDefinition) -> Self {
        let overloads = definition.overloads();
        let mut parent = FxHashMap::<Name, Name>::default();
        fn find(parent: &mut FxHashMap<Name, Name>, name: &Name) -> Name {
            let mut root = name.clone();
            while let Some(next) = parent.get(&root).filter(|next| *next != &root) {
                root = next.clone();
            }
            parent.insert(name.clone(), root.clone());
            root
        }
        for name in definition.symbols().keys() {
            if !overloads.is_overloaded(name) {
                continue;
            }
            parent.entry(name.clone()).or_insert_with(|| name.clone());
            for lesser in overloads.overloaded_by(name) {
                parent
                    .entry(lesser.clone())
                    .or_insert_with(|| lesser.clone());
                let (left, right) = (find(&mut parent, name), find(&mut parent, &lesser));
                if left != right {
                    parent.insert(left, right);
                }
            }
        }
        let mut names = parent.keys().cloned().collect::<Vec<_>>();
        names.sort();
        let mut index_of_root = FxHashMap::<Name, usize>::default();
        let mut families = Self::default();
        for name in names {
            let root = find(&mut parent, &name);
            let next = families.members.len();
            let index = *index_of_root.entry(root).or_insert(next);
            if index == families.members.len() {
                families.members.push(Vec::new());
                families.confluent.push(false);
            }
            families.members[index].push(name.clone());
            families.family_of.insert(name, index);
        }
        families
    }

    /// The family `symbol` belongs to, if any.
    pub(crate) fn family(&self, symbol: &Name) -> Option<usize> {
        self.family_of.get(symbol).copied()
    }

    /// The members of family `family`, sorted by name.
    pub(crate) fn members(&self, family: usize) -> &[Name] {
        &self.members[family]
    }

    /// The number of families.
    pub(crate) fn len(&self) -> usize {
        self.members.len()
    }

    /// Record that family `family` is confluent.
    pub(crate) fn set_confluent(&mut self, family: usize) {
        self.confluent[family] = true;
    }

    /// Whether family `family` is known confluent.
    pub(crate) fn is_confluent(&self, family: usize) -> bool {
        self.confluent[family]
    }
}

/// One unification problem's settings and counters.
pub(crate) struct Unifier<'a> {
    pub(crate) definition: &'a BackendDefinition,
    pub(crate) families: &'a Families,
    /// Whether the overload axioms of confluent families may be used (stage 2). Stage 1 sets
    /// it to `false`: comparisons that need lifting then answer [`UnresolvedShape::Family`].
    pub(crate) lifting: bool,
    /// Whether a term is a normal form on every instance the caller asks about.
    pub(crate) known_normal: &'a dyn Fn(&Term) -> bool,
    /// The counter fresh variable names are minted from; shared by every unification of one
    /// check, so that no two fresh variables of one check share a name.
    pub(crate) fresh: &'a mut u64,
    /// Branch states explored, for the check's counters.
    pub(crate) branches: usize,
    /// Whether an equation of a shape the unifier does not decide (a collection or a function
    /// application, [`UnresolvedShape::Collection`] and [`UnresolvedShape::Function`]) is dropped
    /// instead of answering that shape ([`Self::unify_all_relaxed`]).
    pub(crate) defer: bool,
}

#[derive(Clone, Debug, Default)]
struct Problem {
    bindings: Substitution,
    equations: Vec<(Term, Term)>,
    /// The shape of the first equation dropped (deferred) from this problem, if any.
    deferred: Option<UnresolvedShape>,
    /// Map equations with no key written alike on both sides yet, waiting for the other
    /// equations' bindings ([`Unifier::maps`]).
    postponed: Vec<(Term, Term)>,
    /// The number of bindings when the postponed equations were last taken up again, and
    /// whether they were then taken up as a last resort (no binding since the round before).
    retried_at: Option<usize>,
    last_resort: bool,
}

impl Problem {
    /// Bind `variable` to `value` after the occurs check, applying the binding to every
    /// remaining equation and earlier binding; `false` when `variable` occurs in `value`, which
    /// has no solution: `value` is built from patterns, whose instances are finite terms.
    fn bind(&mut self, variable: &Variable, value: Term) -> bool {
        if let TermKind::Variable(other) = value.kind()
            && other == variable
        {
            return true;
        }
        if value.attributes().variables.contains(variable) {
            return false;
        }
        let single = Substitution::from([(variable.clone(), value.clone())]);
        for (left, right) in self.equations.iter_mut().chain(self.postponed.iter_mut()) {
            *left = substitute(left, &single);
            *right = substitute(right, &single);
        }
        for bound in self.bindings.values_mut() {
            *bound = substitute(bound, &single);
        }
        self.bindings.insert(variable.clone(), value);
        self.last_resort = false;
        true
    }
}

/// What one equation became.
enum Outcome {
    /// Replaced by the equations pushed onto the problem, or solved.
    Continue,
    /// No solution.
    Clash,
    /// The problem splits; the current problem is replaced by these.
    Branch(Vec<Problem>),
}

/// ```toml algorithm-site
/// id = "backend.confluence.critical_pairs"
/// role = "part"
/// sites = ["Unifier::unify_all", "Unifier::step"]
/// ```
impl Unifier<'_> {
    /// Every unifier of `left` and `right` over normal-form instances modulo the matching theory,
    /// each idempotent, or the shape that is not decided. An empty list proves that the two have
    /// no common instance.
    pub(crate) fn unify(
        &mut self,
        left: &Term,
        right: &Term,
    ) -> Result<Vec<Substitution>, UnresolvedShape> {
        self.unify_all(vec![(left.clone(), right.clone())])
    }

    /// [`Self::unify`] for several equations at once.
    pub(crate) fn unify_all(
        &mut self,
        equations: Vec<(Term, Term)>,
    ) -> Result<Vec<Substitution>, UnresolvedShape> {
        let solutions = self.unify_all_relaxed(equations)?;
        match solutions.iter().find_map(|(_, deferred)| deferred.clone()) {
            Some(shape) => Err(shape),
            None => Ok(solutions
                .into_iter()
                .map(|(bindings, _)| bindings)
                .collect()),
        }
    }

    /// [`Self::unify_all`], except that with [`Self::defer`] an equation of a collection or
    /// function shape is dropped from its problem and the problem goes on: each solution comes
    /// with the shape of the first equation dropped from it, if any. Dropping an equation only
    /// enlarges a problem's solutions, so every common instance is still an instance of one
    /// solution (completeness); a solution with a dropped equation (*relaxed*) need not be a
    /// unifier.
    pub(crate) fn unify_all_relaxed(
        &mut self,
        equations: Vec<(Term, Term)>,
    ) -> Result<Vec<(Substitution, Option<UnresolvedShape>)>, UnresolvedShape> {
        let mut stack = vec![Problem {
            bindings: Substitution::new(),
            equations,
            deferred: None,
            postponed: Vec::new(),
            retried_at: None,
            last_resort: false,
        }];
        let mut solutions = Vec::new();
        let mut explored = 0;
        'problems: while let Some(mut problem) = stack.pop() {
            explored += 1;
            self.branches += 1;
            if explored > UNIFIER_BRANCHES {
                return Err(UnresolvedShape::Budget);
            }
            loop {
                while let Some((left, right)) = problem.equations.pop() {
                    match self.step(&mut problem, left, right) {
                        Ok(Outcome::Continue) => {}
                        Ok(Outcome::Clash) => continue 'problems,
                        Ok(Outcome::Branch(branches)) => {
                            stack.extend(branches);
                            continue 'problems;
                        }
                        Err(
                            shape @ (UnresolvedShape::Collection | UnresolvedShape::Function(_)),
                        ) if self.defer => {
                            problem.deferred.get_or_insert(shape);
                        }
                        Err(shape) => return Err(shape),
                    }
                }
                if problem.postponed.is_empty() {
                    break;
                }
                // Keys change only by bindings: with none since the last round, the postponed
                // equations are taken up as a last resort, and answer what they do not decide.
                let bound = problem.bindings.len();
                problem.last_resort = problem.retried_at == Some(bound);
                problem.retried_at = Some(bound);
                let postponed = std::mem::take(&mut problem.postponed);
                problem.equations.extend(postponed);
            }
            solutions.push((problem.bindings, problem.deferred));
        }
        Ok(solutions)
    }

    fn fresh_variable(&mut self, sort: Sort) -> Variable {
        let name = with_fresh_marker("VarOverlap", FreshMarker::Unify, *self.fresh);
        *self.fresh += 1;
        Variable::new(name, sort)
    }

    /// Whether `sub` is below `sup` in the sort order; a sort variable the order cannot decide
    /// is unresolved.
    fn below(&self, sub: &Sort, sup: &Sort) -> Result<bool, UnresolvedShape> {
        self.definition
            .sort_graph()
            .check_subsort(sub, sup)
            .map_err(|_| UnresolvedShape::SortVariable)
    }

    fn maximal_common_subsorts(
        &self,
        left: &Sort,
        right: &Sort,
    ) -> Result<Vec<Sort>, UnresolvedShape> {
        if super::switches::active().drop_glb_branches {
            return Ok(Vec::new());
        }
        self.definition
            .sort_graph()
            .maximal_common_subsorts(left, right)
            .ok_or(UnresolvedShape::SortVariable)
    }

    /// Whether comparisons through the overload axioms of `symbol`'s family are allowed.
    fn may_lift(&self, symbol: &Name) -> Result<(), UnresolvedShape> {
        let family = self.families.family(symbol);
        if self.lifting && family.is_some_and(|family| self.families.is_confluent(family)) {
            Ok(())
        } else {
            Err(UnresolvedShape::Family(symbol.clone()))
        }
    }

    #[deny(clippy::wildcard_enum_match_arm)]
    fn step(
        &mut self,
        problem: &mut Problem,
        left: Term,
        right: Term,
    ) -> Result<Outcome, UnresolvedShape> {
        if left == right {
            return Ok(Outcome::Continue);
        }
        if let TermKind::And(first, second) = left.kind() {
            problem.equations.push((first.clone(), right.clone()));
            problem.equations.push((second.clone(), right));
            return Ok(Outcome::Continue);
        }
        if let TermKind::And(first, second) = right.kind() {
            problem.equations.push((left.clone(), first.clone()));
            problem.equations.push((left, second.clone()));
            return Ok(Outcome::Continue);
        }
        if let TermKind::Variable(variable) = left.kind() {
            return self.variable(problem, variable, &right);
        }
        if let TermKind::Variable(variable) = right.kind() {
            return self.variable(problem, variable, &left);
        }
        let (left_sort, right_sort) = (left.sort(), right.sort());
        if left_sort != right_sort {
            // Values of two sorts are equal only through injections into the greater one.
            if self.below(&left_sort, &right_sort)? {
                problem
                    .equations
                    .push((Term::injection(left_sort, right_sort, left), right));
                return Ok(Outcome::Continue);
            }
            if self.below(&right_sort, &left_sort)? {
                problem
                    .equations
                    .push((left, Term::injection(right_sort, left_sort, right)));
                return Ok(Outcome::Continue);
            }
            // Incomparable sorts have disjoint carriers: a value of one is a value of the other
            // only through injections into a common supersort, which neither term is.
            return Ok(Outcome::Clash);
        }
        match (left.kind(), right.kind()) {
            (TermKind::DomainValue { .. }, TermKind::DomainValue { .. }) => Ok(Outcome::Clash),
            (
                TermKind::Injection {
                    source: left_source,
                    term: left_operand,
                    ..
                },
                TermKind::Injection {
                    source: right_source,
                    term: right_operand,
                    ..
                },
            ) => self.injections(
                problem,
                left_source,
                left_operand,
                right_source,
                right_operand,
            ),
            (TermKind::Application { .. }, TermKind::Application { .. }) => {
                self.applications(problem, &left, &right)
            }
            (TermKind::Application { .. }, TermKind::Injection { .. }) => {
                self.application_and_injection(problem, &left, &right)
            }
            (TermKind::Injection { .. }, TermKind::Application { .. }) => {
                self.application_and_injection(problem, &right, &left)
            }
            (
                TermKind::List {
                    definition: left_definition,
                    heads: left_heads,
                    rest: left_rest,
                },
                TermKind::List {
                    definition: right_definition,
                    heads: right_heads,
                    rest: right_rest,
                },
            ) => {
                if left_definition != right_definition {
                    return Ok(Outcome::Clash);
                }
                Self::lists(
                    problem,
                    left_definition,
                    (left_heads, left_rest.as_ref()),
                    (right_heads, right_rest.as_ref()),
                )
            }
            (TermKind::Map { .. }, TermKind::Map { .. }) => self.maps(problem, &left, &right),
            (TermKind::Set { .. }, TermKind::Set { .. }) => Err(UnresolvedShape::Collection),
            (TermKind::Application { symbol, .. }, _)
            | (_, TermKind::Application { symbol, .. }) => {
                if computed(symbol) {
                    Err(UnresolvedShape::Function(symbol.name.clone()))
                } else {
                    // A constructor or equation-head application against a domain value, a
                    // collection or an injection's absence: different roots.
                    Ok(Outcome::Clash)
                }
            }
            (
                TermKind::DomainValue { .. }
                | TermKind::Injection { .. }
                | TermKind::Map { .. }
                | TermKind::List { .. }
                | TermKind::Set { .. }
                | TermKind::Variable(_)
                | TermKind::And(..),
                TermKind::DomainValue { .. }
                | TermKind::Injection { .. }
                | TermKind::Map { .. }
                | TermKind::List { .. }
                | TermKind::Set { .. }
                | TermKind::Variable(_)
                | TermKind::And(..),
            ) => Ok(Outcome::Clash),
        }
    }

    /// `variable = other`, `other` not a conjunction.
    fn variable(
        &mut self,
        problem: &mut Problem,
        variable: &Variable,
        other: &Term,
    ) -> Result<Outcome, UnresolvedShape> {
        if variable.kind == VariableKind::Set
            || matches!(
                other.kind(),
                TermKind::Variable(Variable {
                    kind: VariableKind::Set,
                    ..
                })
            )
        {
            return Err(UnresolvedShape::SetVariable);
        }
        // A value is one term: the conjunctions of a pattern (aliases) become equations between
        // their conjuncts, and the value keeps the structured conjunct.
        let other = &strip_conjunctions(other, &mut problem.equations);
        let (variable_sort, other_sort) = (&variable.sort, other.sort());
        let solved = |problem: &mut Problem, variable: &Variable, value: Term| {
            if problem.bind(variable, value) {
                Outcome::Continue
            } else {
                Outcome::Clash
            }
        };
        if *variable_sort == other_sort {
            return Ok(solved(problem, variable, other.clone()));
        }
        if self.below(&other_sort, variable_sort)? {
            let value = Term::injection(other_sort, *variable_sort, other.clone());
            return Ok(solved(problem, variable, value));
        }
        if self.below(variable_sort, &other_sort)? {
            let injected =
                Term::injection(*variable_sort, other_sort, Term::variable(variable.clone()));
            if let TermKind::Variable(other_variable) = other.kind() {
                return Ok(solved(problem, other_variable, injected));
            }
            problem.equations.push((injected, other.clone()));
            return Ok(Outcome::Continue);
        }
        let TermKind::Variable(other_variable) = other.kind() else {
            // A variable of one sort against a term of an incomparable sort: disjoint carriers.
            return Ok(Outcome::Clash);
        };
        // Two variables of incomparable sorts denote one value only through a common subsort.
        let commons = self.maximal_common_subsorts(variable_sort, &other_sort)?;
        let mut branches = Vec::new();
        for common in commons {
            let shared = Term::variable(self.fresh_variable(common));
            let mut branch = problem.clone();
            if branch.bind(
                variable,
                Term::injection(common, *variable_sort, shared.clone()),
            ) && branch.bind(other_variable, Term::injection(common, other_sort, shared))
            {
                branches.push(branch);
            }
        }
        Ok(Outcome::Branch(branches))
    }

    /// `inj{A,T}(p) = inj{B,T}(q)`.
    fn injections(
        &mut self,
        problem: &mut Problem,
        left_source: &Sort,
        left: &Term,
        right_source: &Sort,
        right: &Term,
    ) -> Result<Outcome, UnresolvedShape> {
        if left_source == right_source {
            problem.equations.push((left.clone(), right.clone()));
            return Ok(Outcome::Continue);
        }
        if self.below(right_source, left_source)? {
            problem.equations.push((
                left.clone(),
                Term::injection(*right_source, *left_source, right.clone()),
            ));
            return Ok(Outcome::Continue);
        }
        if self.below(left_source, right_source)? {
            problem.equations.push((
                Term::injection(*left_source, *right_source, left.clone()),
                right.clone(),
            ));
            return Ok(Outcome::Continue);
        }
        let commons = self.maximal_common_subsorts(left_source, right_source)?;
        let mut branches = Vec::new();
        for common in commons {
            let shared = Term::variable(self.fresh_variable(common));
            let mut branch = problem.clone();
            branch.equations.push((
                left.clone(),
                Term::injection(common, *left_source, shared.clone()),
            ));
            branch.equations.push((
                right.clone(),
                Term::injection(common, *right_source, shared),
            ));
            branches.push(branch);
        }
        Ok(Outcome::Branch(branches))
    }

    /// Two applications of one sort.
    fn applications(
        &mut self,
        problem: &mut Problem,
        left: &Term,
        right: &Term,
    ) -> Result<Outcome, UnresolvedShape> {
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
            unreachable!("two applications")
        };
        if left_symbol.name == right_symbol.name {
            if left_sorts != right_sorts {
                return if left_sorts.iter().chain(right_sorts).any(has_sort_variable) {
                    Err(UnresolvedShape::SortVariable)
                } else {
                    Ok(Outcome::Clash)
                };
            }
            if left_arguments.len() != right_arguments.len() {
                return Ok(Outcome::Clash);
            }
            problem.equations.extend(
                left_arguments
                    .iter()
                    .cloned()
                    .zip(right_arguments.iter().cloned()),
            );
            return Ok(Outcome::Continue);
        }
        for symbol in [left_symbol, right_symbol] {
            if computed(symbol) {
                return Err(UnresolvedShape::Function(symbol.name.clone()));
            }
        }
        let family = |symbol: &Symbol| self.families.family(&symbol.name);
        if family(left_symbol).is_none() || family(left_symbol) != family(right_symbol) {
            // Different free or equation-head roots outside one family: their applications are
            // different terms modulo the matching theory.
            return Ok(Outcome::Clash);
        }
        if super::switches::active().drop_lifting {
            return Ok(Outcome::Clash);
        }
        self.may_lift(&left_symbol.name)?;
        let overloads = self.definition.overloads();
        let (greater, greater_sorts, lesser) =
            if overloads.is_overloading(&left_symbol.name, &right_symbol.name) {
                (left_symbol, left_sorts, right)
            } else if overloads.is_overloading(&right_symbol.name, &left_symbol.name) {
                (right_symbol, right_sorts, left)
            } else {
                return Err(UnresolvedShape::Family(left_symbol.name.clone()));
            };
        let lifted = lift_to_overload(
            lesser,
            Arc::clone(greater),
            greater_sorts,
            self.definition.sort_graph(),
        )
        .ok_or_else(|| UnresolvedShape::Family(greater.name.clone()))?;
        let other = if Arc::ptr_eq(greater, left_symbol) {
            left
        } else {
            right
        };
        problem.equations.push((other.clone(), lifted));
        Ok(Outcome::Continue)
    }

    /// An application `g(p)` against an injection `inj{S,G}(u)` of one sort `G`.
    fn application_and_injection(
        &mut self,
        problem: &mut Problem,
        application: &Term,
        injection: &Term,
    ) -> Result<Outcome, UnresolvedShape> {
        let TermKind::Application {
            symbol: greater,
            sort_arguments: greater_sorts,
            ..
        } = application.kind()
        else {
            unreachable!("an application")
        };
        let TermKind::Injection {
            source,
            target,
            term: operand,
        } = injection.kind()
        else {
            unreachable!("an injection")
        };
        if computed(greater) {
            return Err(UnresolvedShape::Function(greater.name.clone()));
        }
        let overloads = self.definition.overloads();
        let lessers = overloads.overloaded_by(&greater.name);
        if lessers.is_empty() {
            // No overload axiom gives an application of `g` the value of an injection.
            return Ok(Outcome::Clash);
        }
        if super::switches::active().drop_lifting {
            return Ok(Outcome::Clash);
        }
        self.may_lift(&greater.name)?;
        if (self.known_normal)(application) {
            // A normal form is in lowest form: no overload equation rewrites it to an injection.
            return Ok(Outcome::Clash);
        }
        match operand.kind() {
            TermKind::Application { symbol, .. } => {
                if computed(symbol) {
                    return Err(UnresolvedShape::Function(symbol.name.clone()));
                }
                if !lessers.contains(&symbol.name) {
                    return if self.families.family(&symbol.name)
                        == self.families.family(&greater.name)
                    {
                        Err(UnresolvedShape::Family(greater.name.clone()))
                    } else {
                        Ok(Outcome::Clash)
                    };
                }
                let lifted = lift_to_overload(
                    injection,
                    Arc::clone(greater),
                    greater_sorts,
                    self.definition.sort_graph(),
                )
                .ok_or_else(|| UnresolvedShape::Family(greater.name.clone()))?;
                problem.equations.push((application.clone(), lifted));
                Ok(Outcome::Continue)
            }
            TermKind::Variable(variable) => {
                if variable.kind == VariableKind::Set {
                    return Err(UnresolvedShape::SetVariable);
                }
                let mut branches = Vec::new();
                if super::switches::active().drop_lesser_productions {
                    return Ok(Outcome::Branch(branches));
                }
                for lesser in lessers {
                    let Some(symbol) = self.definition.symbols().get(&lesser) else {
                        return Err(UnresolvedShape::Family(greater.name.clone()));
                    };
                    if !symbol.sort_variables.is_empty() {
                        return Err(UnresolvedShape::SortVariable);
                    }
                    if !self.below(&symbol.result_sort, source)? {
                        continue;
                    }
                    let arguments = symbol
                        .argument_sorts
                        .iter()
                        .map(|sort| Term::variable(self.fresh_variable(*sort)))
                        .collect();
                    let lesser_application =
                        Term::application(Arc::clone(symbol), Vec::new(), arguments);
                    let value = if &symbol.result_sort == source {
                        lesser_application
                    } else {
                        Term::injection(symbol.result_sort, *source, lesser_application)
                    };
                    let mut branch = problem.clone();
                    if !branch.bind(variable, value.clone()) {
                        continue;
                    }
                    let single = Substitution::from([(variable.clone(), value.clone())]);
                    let application = substitute(application, &single);
                    let lifted = lift_to_overload(
                        &Term::injection(*source, *target, value),
                        Arc::clone(greater),
                        greater_sorts,
                        self.definition.sort_graph(),
                    )
                    .ok_or_else(|| UnresolvedShape::Family(greater.name.clone()))?;
                    branch.equations.push((application, lifted));
                    branches.push(branch);
                }
                Ok(Outcome::Branch(branches))
            }
            TermKind::And(first, second) => {
                problem.equations.push((
                    application.clone(),
                    Term::injection(*source, *target, first.clone()),
                ));
                problem.equations.push((
                    application.clone(),
                    Term::injection(*source, *target, second.clone()),
                ));
                Ok(Outcome::Continue)
            }
            TermKind::DomainValue { .. }
            | TermKind::Injection { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. } => Ok(Outcome::Clash),
        }
    }

    /// Two maps of one sort, read over the instances at which both are defined (a defined map
    /// term's explicit keys are pairwise distinct and none is a key of its rest, `term.rs`).
    ///
    /// 1. Size test (P7-KEVM-S2B): a term with `n` explicit entries binds at least `n` keys, and
    ///    exactly `n` without a rest, so the equation clashes when a side without a rest has
    ///    fewer entries than the other.
    /// 2. An entry whose key is written alike on both sides (after the problem's bindings) is
    ///    decomposed: a map binds each key once, so two maps that bind the same key are equal
    ///    exactly when they give it the same value and are equal without it.
    /// 3. What is left: rest = rest when no entry is left; a variable rest of a side with no entry
    ///    left is the other side; otherwise the equation waits for the other equations'
    ///    bindings, and as a last resort (or with an opaque rest) is
    ///    [`UnresolvedShape::Collection`].
    ///
    /// A returned unifier may have instances at which a map repeats a key; both sides are then
    /// `\bottom` and the instance is none. An empty answer proves no common defined instance,
    /// which `classify`, `Join::refuted_at` and `Join::split_on` all read.
    fn maps(
        &mut self,
        problem: &mut Problem,
        left: &Term,
        right: &Term,
    ) -> Result<Outcome, UnresolvedShape> {
        let (
            TermKind::Map {
                definition,
                entries: left_entries,
                rest: left_rest,
            },
            TermKind::Map {
                definition: right_definition,
                entries: right_entries,
                rest: right_rest,
            },
        ) = (left.kind(), right.kind())
        else {
            unreachable!("two maps")
        };
        if definition != right_definition {
            return Err(UnresolvedShape::Collection);
        }
        let switches = super::switches::active();
        // 1. The size test.
        let count = |entries: usize, rest: &Option<Term>| {
            entries + usize::from(switches.size_counts_rest && rest.is_some())
        };
        let (left_count, right_count) = (
            count(left_entries.len(), left_rest),
            count(right_entries.len(), right_rest),
        );
        let closed = |rest: &Option<Term>| rest.is_none() || switches.size_clash_ignores_rest;
        if (closed(left_rest) && left_count < right_count)
            || (closed(right_rest) && right_count < left_count)
        {
            return Ok(Outcome::Clash);
        }
        // 2. Keys written alike.
        let mut left_left: Vec<(Term, Term)> = left_entries.iter().cloned().collect();
        let mut right_left: Vec<(Term, Term)> = right_entries.iter().cloned().collect();
        let mut decomposed = false;
        if switches.decompose_unifiable_keys {
            // Defect: commit to the first pair of keys that are not written alike.
            if !left_left.is_empty()
                && !right_left.is_empty()
                && !left_left
                    .iter()
                    .any(|(key, _)| right_left.iter().any(|(other, _)| key == other))
            {
                let (first, second) = (left_left.remove(0), right_left.remove(0));
                problem.equations.push((first.0, second.0));
                problem.equations.push((first.1, second.1));
                decomposed = true;
            }
        }
        left_left.retain(|(key, value)| {
            match right_left.iter().position(|(other, _)| other == key) {
                Some(position) => {
                    let (_, other_value) = right_left.remove(position);
                    problem.equations.push((value.clone(), other_value));
                    decomposed = true;
                    false
                }
                None => true,
            }
        });
        // 3. What is left.
        let unit = || Term::map(Arc::clone(definition), Vec::new(), None);
        let side = |entries: Vec<(Term, Term)>, rest: &Option<Term>| {
            Term::map(Arc::clone(definition), entries, rest.clone())
        };
        let open = |rest: &Option<Term>| {
            rest.as_ref()
                .is_some_and(|rest| matches!(rest.kind(), TermKind::Variable(_)))
        };
        match (left_left.is_empty(), right_left.is_empty()) {
            (true, true) => {
                problem.equations.push((
                    left_rest.clone().unwrap_or_else(unit),
                    right_rest.clone().unwrap_or_else(unit),
                ));
                return Ok(Outcome::Continue);
            }
            (true, false) | (false, true) => {
                if switches.empty_clash_ignores_rest {
                    return Ok(Outcome::Clash);
                }
                let (empty_rest, other, other_rest) = if left_left.is_empty() {
                    (left_rest, right_left, right_rest)
                } else {
                    (right_rest, left_left, left_rest)
                };
                match empty_rest {
                    // Not reached: the size test clashed (both counts fell by the same number).
                    None => return Ok(Outcome::Clash),
                    Some(rest) if open(empty_rest) => {
                        let other_rest = if switches.rest_binding_drops_rest {
                            &None
                        } else {
                            other_rest
                        };
                        problem
                            .equations
                            .push((rest.clone(), side(other, other_rest)));
                        return Ok(Outcome::Continue);
                    }
                    Some(_) => {
                        return if switches.raw_rest_clashes {
                            Ok(Outcome::Clash)
                        } else {
                            Err(UnresolvedShape::Collection)
                        };
                    }
                }
            }
            (false, false) => {}
        }
        let remainder = (side(left_left, left_rest), side(right_left, right_rest));
        if decomposed || !problem.last_resort {
            problem.postponed.push(remainder);
            Ok(Outcome::Continue)
        } else if switches.last_resort_clashes {
            Ok(Outcome::Clash)
        } else {
            Err(UnresolvedShape::Collection)
        }
    }

    /// Two lists of one definition: `heads`, then the optional `(middle, tails)`.
    fn lists(
        problem: &mut Problem,
        definition: &Arc<ListDefinition>,
        left: (&Items<Term>, Option<&(Term, Items<Term>)>),
        right: (&Items<Term>, Option<&(Term, Items<Term>)>),
    ) -> Result<Outcome, UnresolvedShape> {
        let list = |heads: Vec<Term>, rest: Option<(Term, Vec<Term>)>| {
            Term::list(Arc::clone(definition), heads, rest)
        };
        match (left, right) {
            ((left_heads, None), (right_heads, None)) => {
                if left_heads.len() != right_heads.len() {
                    return Ok(Outcome::Clash);
                }
                problem
                    .equations
                    .extend(left_heads.iter().cloned().zip(right_heads.iter().cloned()));
                Ok(Outcome::Continue)
            }
            ((open_heads, Some((middle, tails))), (closed, None))
            | ((closed, None), (open_heads, Some((middle, tails)))) => {
                // A list with fixed elements at both ends and a middle against a closed list:
                // the middle is what is left between them.
                if open_heads.len() + tails.len() > closed.len() {
                    return Ok(Outcome::Clash);
                }
                let middle_end = closed.len() - tails.len();
                problem
                    .equations
                    .extend(open_heads.iter().cloned().zip(closed.iter().cloned()));
                problem.equations.extend(
                    tails
                        .iter()
                        .cloned()
                        .zip(closed.range(middle_end..).cloned()),
                );
                problem.equations.push((
                    middle.clone(),
                    list(
                        closed
                            .range(open_heads.len()..middle_end)
                            .cloned()
                            .collect(),
                        None,
                    ),
                ));
                Ok(Outcome::Continue)
            }
            (
                (left_heads, Some((left_middle, left_tails))),
                (right_heads, Some((right_middle, right_tails))),
            ) => {
                if left_tails.is_empty() && right_tails.is_empty() {
                    // Elements fixed at the front only: the shorter prefix is matched elementwise
                    // and its rest absorbs the longer one's remaining elements (unitary modulo
                    // associativity and unit).
                    let shared = left_heads.len().min(right_heads.len());
                    problem.equations.extend(
                        left_heads
                            .range(..shared)
                            .cloned()
                            .zip(right_heads.range(..shared).cloned()),
                    );
                    let (short_middle, long_heads, long_middle) =
                        if left_heads.len() <= right_heads.len() {
                            (left_middle, right_heads, right_middle)
                        } else {
                            (right_middle, left_heads, left_middle)
                        };
                    problem.equations.push((
                        short_middle.clone(),
                        list(
                            long_heads.range(shared..).cloned().collect(),
                            Some((long_middle.clone(), Vec::new())),
                        ),
                    ));
                    Ok(Outcome::Continue)
                } else if left_heads.is_empty() && right_heads.is_empty() {
                    // Elements fixed at the back only: symmetric.
                    let shared = left_tails.len().min(right_tails.len());
                    problem.equations.extend(
                        left_tails
                            .range(left_tails.len() - shared..)
                            .cloned()
                            .zip(right_tails.range(right_tails.len() - shared..).cloned()),
                    );
                    let (short_middle, long_tails, long_middle) =
                        if left_tails.len() <= right_tails.len() {
                            (left_middle, right_tails, right_middle)
                        } else {
                            (right_middle, left_tails, left_middle)
                        };
                    problem.equations.push((
                        short_middle.clone(),
                        list(
                            Vec::new(),
                            Some((
                                long_middle.clone(),
                                long_tails
                                    .range(..long_tails.len() - shared)
                                    .cloned()
                                    .collect(),
                            )),
                        ),
                    ));
                    Ok(Outcome::Continue)
                } else {
                    Err(UnresolvedShape::Collection)
                }
            }
        }
    }
}

/// `term` with every `\and(a, b)` replaced by its structured conjunct (`b` when `a` is a
/// variable, else `a`), each pair of conjuncts pushed onto `equations`.
fn strip_conjunctions(term: &Term, equations: &mut Vec<(Term, Term)>) -> Term {
    if !contains_conjunction(term) {
        return term.clone();
    }
    if let TermKind::And(left, right) = term.kind() {
        equations.push((left.clone(), right.clone()));
        let kept = if matches!(left.kind(), TermKind::Variable(_)) {
            right
        } else {
            left
        };
        return strip_conjunctions(kept, equations);
    }
    let children = super::children(term)
        .iter()
        .map(|child| strip_conjunctions(child, equations))
        .collect();
    super::with_children(term, children)
}

fn contains_conjunction(term: &Term) -> bool {
    matches!(term.kind(), TermKind::And(..))
        || super::children(term).iter().any(contains_conjunction)
}

/// Whether `symbol`'s applications are computed rather than individuated: a declared function, a
/// macro or alias, or an uninterpreted symbol.
#[deny(clippy::wildcard_enum_match_arm)]
pub(crate) fn computed(symbol: &Symbol) -> bool {
    match symbol.attributes.head_role() {
        HeadRole::FreeConstructor | HeadRole::EquationHead => false,
        HeadRole::Function { .. } | HeadRole::Residual | HeadRole::Uninterpreted => true,
    }
}

fn has_sort_variable(sort: &Sort) -> bool {
    match sort.node() {
        SortNode::Variable(_) => true,
        SortNode::Application { arguments, .. } => arguments.iter().any(has_sort_variable),
    }
}
