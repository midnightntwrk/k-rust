//! ```toml algorithm
//! id = "backend.fresh.variables"
//! name = "request-scoped variable naming with collision retry"
//! sites = ["FreshCounter::mint", "fresh_name", "fresh_variable"]
//! variable = "c = colliding candidate names; v = variable names collected into a site's avoid set"
//! counters = []
//! no_counter = "fresh backend variable naming has no dedicated counter"
//! span = "none"
//!
//! [[cost]]
//! mode = "request counter"
//! bound = "O(c log v) per name, amortized O(log v) with one growing counter per request"
//!
//! [[cost]]
//! mode = "local counter"
//! bound = "O(c) per name, amortized O(1)"
//!
//! [[cost]]
//! mode = "avoid-set construction at a site (freshen_existentials, mint_unbound_rule_variables, freshen_claim, rename_apart, alias fresh_variable)"
//! bound = "O(v log v) per call before the retry loop"
//!
//! [[cost]]
//! mode = "state and solution keys (RequestNames::state_key, RequestNames::solution_key)"
//! bound = "O(n + v log v) for a pattern of n nodes and v variables, plus O(k log k) blind comparisons for each map or set of k elements holding a variable not yet met, each at most the size of the smaller element, plus sorting the c constraints, O(c log c) comparisons"
//!
//! [[cost]]
//! mode = "freshen_existentials"
//! bound = "O(c) per name without amortization, since the suffix restarts at each existential's index"
//! ```
//!
//! Counter-suffixed fresh variable naming with collision retry against a name set, the one home
//! for backend-term names (alias unfolding keeps its own `{name}Alias{index}` loop in `alias.rs`,
//! a declared variant): one loop, O(collisions) per name; no measurement counter. The spelling is
//! `term::names::with_fresh_marker` (`{base}!{marker}{counter}`; marker `""` for variables a
//! rewrite introduces, `claim` for claim variables, `exists` for implication existentials,
//! `binder` for renamed quantifier variables).
//!
//! A variable a rewrite introduces into a state (a right-hand-side existential, a rule variable
//! the match left unbound, a narrowed collection frame) or a claim variable a proof renames is
//! minted by the request's [`FreshCounter`]: one counter that only grows through the request, so
//! no two such names of a request share a counter, and a name never denotes a second variable
//! after the first one left the state. The counter skips every candidate spelled like a variable
//! of the request ([`RequestNames`]), so no mint prints like a name of the request either.
//! Rule variables renamed apart from an application's scope (`rule::rename_apart`) use marker
//! `apart` with the counter of the enclosing request (`rule::ApartScope`); the other local
//! markers name variables bound inside one predicate or one check.
//!
//! Because the counter names every introduced variable apart, two states that one search or
//! execution reaches twice differ in those names; `RequestNames::state_key` and
//! `RequestNames::solution_key` identify states, search solutions, and state-set leaves up to
//! them.

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::{
    rewrite::Pattern,
    rule::{Predicate, collect_all_variables, rename_predicates},
    substitution::{Substitution, substitute},
    term::{
        Name, Term, TermKind, Variable,
        names::{FreshMarker, encode_variable_name, with_fresh_marker},
    },
};

/// The printed spellings of every variable, free or bound, of the patterns of one request.
///
/// A name read from KORE never equals a name the backend makes (`term::names`), but it may be
/// spelled like one: a request variable named `Ex-hX-b0` prints like the mint `Ex#X!0`. A name
/// that the backend introduces into a response must therefore avoid the spellings of the
/// request, not only its names, or the response would print two variables alike. Bound names
/// count too: a mint may be substituted under a request binder of its spelling.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RequestNames(Arc<BTreeSet<String>>);

impl RequestNames {
    /// The spellings of every variable of `patterns`, free or bound.
    pub fn of(patterns: &[&Pattern]) -> Self {
        let mut names = Self::default();
        for pattern in patterns {
            names.add_pattern(pattern);
        }
        names
    }

    /// Add the spellings of every variable of `pattern`, free or bound.
    pub fn add_pattern(&mut self, pattern: &Pattern) {
        let mut variables = pattern.term.attributes().variables.clone();
        collect_all_variables(&pattern.constraints, &mut variables);
        self.add_variables(&variables);
    }

    /// Add the spellings of `variables`.
    pub fn add_variables<'a>(&mut self, variables: impl IntoIterator<Item = &'a Variable>) {
        let spellings = Arc::make_mut(&mut self.0);
        spellings.extend(
            variables
                .into_iter()
                .map(|variable| encode_variable_name(&variable.name)),
        );
    }

    /// Add the spellings of every name of `other`.
    pub fn extend(&mut self, other: &Self) {
        if !other.0.is_empty() {
            Arc::make_mut(&mut self.0).extend(other.0.iter().cloned());
        }
    }

    /// Whether some variable of the request prints as `name` prints.
    pub fn spells(&self, name: &str) -> bool {
        !self.0.is_empty() && self.0.contains(&encode_variable_name(name))
    }

    /// `pattern` as a state of this request whatever names the request's counter gave its
    /// other variables: the pattern under [`RequestNames::canonical_renaming`], its constraints
    /// sorted (a conjunction, so their order does not change what the state denotes).
    ///
    /// A variable of a state that the request does not name was introduced into it by a
    /// rewrite (a right-hand-side existential, a rule variable the match left unbound, a
    /// narrowed frame) or is bound inside it. Either way it is quantified over that state
    /// alone (docs/compatibility.md#result-variables), so an injective renaming of such
    /// variables that fixes the request's names gives a state that denotes the same
    /// configurations and whose successors are the renamed successors. Two states with equal
    /// keys are such renamings of each other, up to the order of conjuncts: each key is its
    /// state under an injective renaming that fixes the request's names, so the second state
    /// is the first under the first key's renaming followed by the inverse of the second's.
    /// Equal states have equal keys, so the key identifies at least the states that are
    /// syntactically equal.
    pub(crate) fn state_key(&self, pattern: &Pattern) -> Pattern {
        let renaming = self.canonical_renaming(&[], &[&pattern.term], &pattern.constraints);
        Pattern {
            term: renaming.term(&pattern.term),
            constraints: renaming.constraints(&pattern.constraints),
        }
    }

    /// A solution of a pattern search, the substitution of the target's variables and the
    /// constraints under which the state matches, whatever names the request's counter gave the
    /// state's other variables: both under one [`RequestNames::canonical_renaming`], the
    /// constraints sorted.
    ///
    /// A variable of the solution that the request does not name is a variable of the matched
    /// state the request does not name, so it is quantified over that solution alone, as in
    /// [`RequestNames::state_key`]: two solutions with equal keys are injective renamings of each
    /// other that fix the request's names, and denote the same instances of the target.
    pub(crate) fn solution_key(
        &self,
        substitution: &Substitution,
        constraints: &[Predicate],
    ) -> SolutionKey {
        let bound = substitution.keys().collect::<Vec<_>>();
        let values = substitution.values().collect::<Vec<_>>();
        let renaming = self.canonical_renaming(&bound, &values, constraints);
        let substitution = substitution
            .iter()
            .map(|(variable, value)| (renaming.variable(variable), renaming.term(value)))
            .collect();
        (substitution, renaming.constraints(constraints))
    }

    /// An injective renaming of the variables of `variables`, `terms` and `predicates` (free or
    /// bound) that no variable of the request is spelled as, to `!{index}`, numbered by first
    /// occurrence: `variables`, then each term in preorder, then the predicates, a binder
    /// before its body. No name of the backend has an empty base (`term::names`), so `!{index}`
    /// captures no variable of them.
    ///
    /// The numbering should not depend on the names it replaces, so that two renamings of one
    /// state receive one key. The elements of a map or a set, and the predicates of a
    /// conjunction or a disjunction, are stored in an order that compares names, so the walk
    /// visits them in [`RequestNames::blind_cmp`] order instead, which compares the variables
    /// it renames by kind and sort only. Elements that order cannot tell apart (they differ
    /// only in the names of renamed variables, or in the stored order of a collection or
    /// connective nested inside them) keep their stored order, so two renamings of one state
    /// can still receive different keys there: the key may identify fewer states than it
    /// could, never two states that are not renamings of each other.
    fn canonical_renaming(
        &self,
        variables: &[&Variable],
        terms: &[&Term],
        predicates: &[Predicate],
    ) -> CanonicalRenaming {
        let mut order = FirstOccurrence {
            request: self,
            seen: BTreeSet::new(),
            renamed: Vec::new(),
        };
        for variable in variables {
            order.variable(variable);
        }
        for term in terms {
            order.term(term);
        }
        order.predicates(predicates.iter());
        let renaming = order
            .renamed
            .into_iter()
            .enumerate()
            .map(|(index, variable)| {
                let renamed = variable.with_name(format!("!{index}"));
                (variable, renamed)
            })
            .collect::<BTreeMap<_, _>>();
        let substitution = renaming
            .iter()
            .map(|(variable, renamed)| (variable.clone(), Term::variable(renamed.clone())))
            .collect::<Substitution>();
        CanonicalRenaming {
            renaming,
            substitution,
        }
    }

    /// Whether the key renames `variable`: no variable of the request is spelled as it is.
    fn renames(&self, variable: &Variable) -> bool {
        !self.spells(&variable.name)
    }

    /// A total preorder on terms and predicates that compares a variable the key renames by its
    /// kind and sort only, and is otherwise structural: it does not change when the variables
    /// the key renames are renamed injectively among themselves. Collection elements and
    /// connective operands are compared in their stored order. The walk keeps an explicit
    /// stack, so a deep term does not deepen the call stack.
    fn blind_cmp(&self, first: Blind<'_>, second: Blind<'_>) -> Ordering {
        let mut pending = vec![(first, second)];
        // Invariant: every pair before the ones in `pending` compared equal, and `pending`
        // holds, last first, the pairs still to compare in preorder.
        while let Some(pair) = pending.pop() {
            let ordering = match pair {
                (Blind::Term(left), Blind::Term(right)) => {
                    self.blind_term_step(left, right, &mut pending)
                }
                (Blind::Predicate(left), Blind::Predicate(right)) => {
                    self.blind_predicate_step(left, right, &mut pending)
                }
                (Blind::Term(_), Blind::Predicate(_)) => Ordering::Less,
                (Blind::Predicate(_), Blind::Term(_)) => Ordering::Greater,
            };
            if ordering.is_ne() {
                return ordering;
            }
        }
        Ordering::Equal
    }

    fn blind_variable_cmp(&self, left: &Variable, right: &Variable) -> Ordering {
        left.kind
            .cmp(&right.kind)
            .then_with(|| left.sort.cmp(&right.sort))
            .then_with(|| match (self.renames(left), self.renames(right)) {
                (true, true) => Ordering::Equal,
                (true, false) => Ordering::Less,
                (false, true) => Ordering::Greater,
                (false, false) => left.name.cmp(&right.name),
            })
    }

    /// Compare the roots of `left` and `right`; when they are equal, queue their children.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn blind_term_step<'a>(
        &self,
        left: &'a Term,
        right: &'a Term,
        pending: &mut Vec<(Blind<'a>, Blind<'a>)>,
    ) -> Ordering {
        if std::ptr::eq(left.kind(), right.kind()) {
            return Ordering::Equal;
        }
        let rank = |term: &Term| match term.kind() {
            TermKind::And(..) => 0u8,
            TermKind::Application { .. } => 1,
            TermKind::DomainValue { .. } => 2,
            TermKind::Variable(_) => 3,
            TermKind::Injection { .. } => 4,
            TermKind::Map { .. } => 5,
            TermKind::List { .. } => 6,
            TermKind::Set { .. } => 7,
        };
        let mut children = Vec::new();
        let ordering = match (left.kind(), right.kind()) {
            (TermKind::And(left_first, left_second), TermKind::And(right_first, right_second)) => {
                children.extend([(left_first, right_first), (left_second, right_second)]);
                Ordering::Equal
            }
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
                children.extend(left_arguments.iter().zip(right_arguments));
                left_symbol
                    .cmp(right_symbol)
                    .then_with(|| left_sorts.cmp(right_sorts))
                    .then_with(|| left_arguments.len().cmp(&right_arguments.len()))
            }
            (
                TermKind::DomainValue {
                    sort: left_sort,
                    value: left_value,
                },
                TermKind::DomainValue {
                    sort: right_sort,
                    value: right_value,
                },
            ) => left_sort
                .cmp(right_sort)
                .then_with(|| left_value.cmp(right_value)),
            (TermKind::Variable(left), TermKind::Variable(right)) => {
                self.blind_variable_cmp(left, right)
            }
            (
                TermKind::Injection {
                    source: left_source,
                    target: left_target,
                    term: left_term,
                },
                TermKind::Injection {
                    source: right_source,
                    target: right_target,
                    term: right_term,
                },
            ) => {
                children.push((left_term, right_term));
                left_source
                    .cmp(right_source)
                    .then_with(|| left_target.cmp(right_target))
            }
            (
                TermKind::Map {
                    definition: left_definition,
                    entries: left_entries,
                    rest: left_rest,
                },
                TermKind::Map {
                    definition: right_definition,
                    entries: right_entries,
                    rest: right_rest,
                },
            ) => {
                for ((left_key, left_value), (right_key, right_value)) in
                    left_entries.iter().zip(right_entries)
                {
                    children.extend([(left_key, right_key), (left_value, right_value)]);
                }
                children.extend(left_rest.iter().zip(right_rest));
                left_definition
                    .cmp(right_definition)
                    .then_with(|| left_entries.len().cmp(&right_entries.len()))
                    .then_with(|| left_rest.is_some().cmp(&right_rest.is_some()))
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
                children.extend(left_heads.iter().zip(right_heads));
                if let (Some((left_middle, left_tails)), Some((right_middle, right_tails))) =
                    (left_rest, right_rest)
                {
                    children.push((left_middle, right_middle));
                    children.extend(left_tails.iter().zip(right_tails));
                }
                let shape =
                    |rest: &Option<(Term, Vec<Term>)>| rest.as_ref().map(|(_, tails)| tails.len());
                left_definition
                    .cmp(right_definition)
                    .then_with(|| left_heads.len().cmp(&right_heads.len()))
                    .then_with(|| shape(left_rest).cmp(&shape(right_rest)))
            }
            (
                TermKind::Set {
                    definition: left_definition,
                    elements: left_elements,
                    rest: left_rest,
                },
                TermKind::Set {
                    definition: right_definition,
                    elements: right_elements,
                    rest: right_rest,
                },
            ) => {
                children.extend(left_elements.iter().zip(right_elements));
                children.extend(left_rest.iter().zip(right_rest));
                left_definition
                    .cmp(right_definition)
                    .then_with(|| left_elements.len().cmp(&right_elements.len()))
                    .then_with(|| left_rest.is_some().cmp(&right_rest.is_some()))
            }
            (
                TermKind::And(..)
                | TermKind::Application { .. }
                | TermKind::DomainValue { .. }
                | TermKind::Variable(_)
                | TermKind::Injection { .. }
                | TermKind::Map { .. }
                | TermKind::List { .. }
                | TermKind::Set { .. },
                _,
            ) => rank(left).cmp(&rank(right)),
        };
        if ordering.is_eq() {
            pending.extend(
                children
                    .into_iter()
                    .rev()
                    .map(|(left, right)| (Blind::Term(left), Blind::Term(right))),
            );
        }
        ordering
    }

    /// Compare the roots of `left` and `right`; when they are equal, queue their operands.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn blind_predicate_step<'a>(
        &self,
        left: &'a Predicate,
        right: &'a Predicate,
        pending: &mut Vec<(Blind<'a>, Blind<'a>)>,
    ) -> Ordering {
        let rank = |predicate: &Predicate| match predicate {
            Predicate::True => 0u8,
            Predicate::False => 1,
            Predicate::Term(_) => 2,
            Predicate::Equals(..) => 3,
            Predicate::Ceil(_) => 4,
            Predicate::Floor(_) => 5,
            Predicate::In(..) => 6,
            Predicate::Not(_) => 7,
            Predicate::And(_) => 8,
            Predicate::Or(_) => 9,
            Predicate::Implies(..) => 10,
            Predicate::Iff(..) => 11,
            Predicate::Exists(..) => 12,
            Predicate::Forall(..) => 13,
        };
        let mut children = Vec::new();
        let ordering = match (left, right) {
            (Predicate::True, Predicate::True) | (Predicate::False, Predicate::False) => {
                Ordering::Equal
            }
            (Predicate::Term(left), Predicate::Term(right))
            | (Predicate::Ceil(left), Predicate::Ceil(right))
            | (Predicate::Floor(left), Predicate::Floor(right)) => {
                children.push((Blind::Term(left), Blind::Term(right)));
                Ordering::Equal
            }
            (
                Predicate::Equals(left_first, left_second),
                Predicate::Equals(right_first, right_second),
            )
            | (Predicate::In(left_first, left_second), Predicate::In(right_first, right_second)) => {
                children.extend([
                    (Blind::Term(left_first), Blind::Term(right_first)),
                    (Blind::Term(left_second), Blind::Term(right_second)),
                ]);
                Ordering::Equal
            }
            (Predicate::Not(left), Predicate::Not(right)) => {
                children.push((Blind::Predicate(left), Blind::Predicate(right)));
                Ordering::Equal
            }
            (Predicate::And(left), Predicate::And(right))
            | (Predicate::Or(left), Predicate::Or(right)) => {
                children.extend(
                    left.iter()
                        .zip(right)
                        .map(|(left, right)| (Blind::Predicate(left), Blind::Predicate(right))),
                );
                left.len().cmp(&right.len())
            }
            (
                Predicate::Implies(left_first, left_second),
                Predicate::Implies(right_first, right_second),
            )
            | (
                Predicate::Iff(left_first, left_second),
                Predicate::Iff(right_first, right_second),
            ) => {
                children.extend([
                    (Blind::Predicate(left_first), Blind::Predicate(right_first)),
                    (
                        Blind::Predicate(left_second),
                        Blind::Predicate(right_second),
                    ),
                ]);
                Ordering::Equal
            }
            (
                Predicate::Exists(left_binder, left_body),
                Predicate::Exists(right_binder, right_body),
            )
            | (
                Predicate::Forall(left_binder, left_body),
                Predicate::Forall(right_binder, right_body),
            ) => {
                children.push((Blind::Predicate(left_body), Blind::Predicate(right_body)));
                self.blind_variable_cmp(left_binder, right_binder)
            }
            (
                Predicate::True
                | Predicate::False
                | Predicate::Term(_)
                | Predicate::Equals(..)
                | Predicate::Ceil(_)
                | Predicate::Floor(_)
                | Predicate::In(..)
                | Predicate::Not(_)
                | Predicate::And(_)
                | Predicate::Or(_)
                | Predicate::Implies(..)
                | Predicate::Iff(..)
                | Predicate::Exists(..)
                | Predicate::Forall(..),
                _,
            ) => rank(left).cmp(&rank(right)),
        };
        if ordering.is_eq() {
            pending.extend(children.into_iter().rev());
        }
        ordering
    }

    /// `items` in [`RequestNames::blind_cmp`] order; equal items keep their stored order.
    fn blind_order<'a, T>(
        &self,
        items: impl IntoIterator<Item = &'a T>,
        blind: impl Fn(&'a T) -> Blind<'a>,
    ) -> Vec<&'a T> {
        let mut items = items.into_iter().collect::<Vec<_>>();
        if items.len() > 1 {
            items.sort_by(|left, right| self.blind_cmp(blind(left), blind(right)));
        }
        items
    }
}

/// The key of a pattern-search solution ([`RequestNames::solution_key`]).
pub(crate) type SolutionKey = (Substitution, Vec<Predicate>);

/// A term or a predicate, as [`RequestNames::blind_cmp`] compares them.
#[derive(Clone, Copy)]
enum Blind<'a> {
    Term(&'a Term),
    Predicate(&'a Predicate),
}

/// The renaming [`RequestNames::canonical_renaming`] chose.
struct CanonicalRenaming {
    renaming: BTreeMap<Variable, Variable>,
    substitution: Substitution,
}

impl CanonicalRenaming {
    fn variable(&self, variable: &Variable) -> Variable {
        self.renaming
            .get(variable)
            .cloned()
            .unwrap_or_else(|| variable.clone())
    }

    fn term(&self, term: &Term) -> Term {
        if self.substitution.is_empty() {
            term.clone()
        } else {
            substitute(term, &self.substitution)
        }
    }

    /// `predicates` renamed, with the operands of every conjunction and disjunction and the
    /// predicates themselves sorted and deduplicated: each list is a conjunction or a
    /// disjunction, so neither its order nor a repeated operand changes what it denotes.
    fn constraints(&self, predicates: &[Predicate]) -> Vec<Predicate> {
        let mut renamed = if self.renaming.is_empty() {
            predicates.to_vec()
        } else {
            rename_predicates(predicates, |variable| self.variable(variable))
        };
        for predicate in &mut renamed {
            sort_operands(predicate);
        }
        renamed.sort();
        renamed.dedup();
        renamed
    }
}

/// Sort and deduplicate the operands of every conjunction and disjunction in `predicate`.
#[deny(clippy::wildcard_enum_match_arm)]
fn sort_operands(predicate: &mut Predicate) {
    match predicate {
        Predicate::True
        | Predicate::False
        | Predicate::Term(_)
        | Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..) => {}
        Predicate::Not(inner) | Predicate::Exists(_, inner) | Predicate::Forall(_, inner) => {
            sort_operands(inner);
        }
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            sort_operands(left);
            sort_operands(right);
        }
        Predicate::And(operands) | Predicate::Or(operands) => {
            for operand in operands.iter_mut() {
                sort_operands(operand);
            }
            operands.sort();
            operands.dedup();
        }
    }
}

/// The variables of a pattern that a request does not name, in order of first occurrence.
struct FirstOccurrence<'a> {
    request: &'a RequestNames,
    /// Every variable met so far, named by the request or not.
    seen: BTreeSet<Variable>,
    /// The variables met so far that the request does not name, in order of first occurrence.
    renamed: Vec<Variable>,
}

impl FirstOccurrence<'_> {
    fn variable(&mut self, variable: &Variable) {
        if self.seen.insert(variable.clone()) && self.request.renames(variable) {
            self.renamed.push(variable.clone());
        }
    }

    /// The variables of `term` in preorder, the elements of a map or a set in
    /// [`RequestNames::blind_cmp`] order. A subterm whose variables were all met is skipped,
    /// so a subterm shared at several positions is walked once per variable it first holds,
    /// and the walk keeps an explicit stack, so a deep term does not deepen the call stack.
    fn term(&mut self, term: &Term) {
        let request = self.request;
        let mut pending = vec![term];
        // Invariant: `pending` holds, last first, the subterms still to walk in preorder.
        while let Some(term) = pending.pop() {
            if term
                .attributes()
                .variables
                .iter()
                .all(|variable| self.seen.contains(variable))
            {
                continue;
            }
            match term.kind() {
                TermKind::Variable(variable) => self.variable(variable),
                TermKind::DomainValue { .. } => {}
                TermKind::And(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                TermKind::Application { arguments, .. } => pending.extend(arguments.iter().rev()),
                TermKind::Injection { term, .. } => pending.push(term),
                TermKind::Map { entries, rest, .. } => {
                    pending.extend(rest);
                    let mut entries = entries.iter().collect::<Vec<_>>();
                    if entries.len() > 1 {
                        entries.sort_by(|(left_key, left_value), (right_key, right_value)| {
                            request
                                .blind_cmp(Blind::Term(left_key), Blind::Term(right_key))
                                .then_with(|| {
                                    request.blind_cmp(
                                        Blind::Term(left_value),
                                        Blind::Term(right_value),
                                    )
                                })
                        });
                    }
                    for (key, value) in entries.into_iter().rev() {
                        pending.push(value);
                        pending.push(key);
                    }
                }
                TermKind::List { heads, rest, .. } => {
                    if let Some((middle, tails)) = rest {
                        pending.extend(tails.iter().rev());
                        pending.push(middle);
                    }
                    pending.extend(heads.iter().rev());
                }
                TermKind::Set { elements, rest, .. } => {
                    pending.extend(rest);
                    let elements = request.blind_order(elements, Blind::Term);
                    pending.extend(elements.into_iter().rev());
                }
            }
        }
    }

    /// The variables of `predicates` in [`RequestNames::blind_cmp`] order.
    fn predicates<'p>(&mut self, predicates: impl IntoIterator<Item = &'p Predicate>) {
        for predicate in self.request.blind_order(predicates, Blind::Predicate) {
            self.predicate(predicate);
        }
    }

    fn predicate(&mut self, predicate: &Predicate) {
        match predicate {
            Predicate::True | Predicate::False => {}
            Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Floor(term) => {
                self.term(term);
            }
            Predicate::Equals(left, right) | Predicate::In(left, right) => {
                self.term(left);
                self.term(right);
            }
            Predicate::Not(inner) => self.predicate(inner),
            Predicate::And(inner) | Predicate::Or(inner) => self.predicates(inner),
            Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
                self.predicate(left);
                self.predicate(right);
            }
            Predicate::Exists(binder, body) | Predicate::Forall(binder, body) => {
                self.variable(binder);
                self.predicate(body);
            }
        }
    }
}

/// The first `{base}!{marker}{counter}` not in `avoid`, added to `avoid`; `counter` ends one
/// past the value that was used.
pub(crate) fn fresh_name(
    base: &str,
    marker: FreshMarker,
    counter: &mut u64,
    avoid: &mut BTreeSet<Name>,
) -> String {
    fresh_name_apart(base, marker, counter, avoid, &RequestNames::default())
}

/// [`fresh_name`], skipping also every candidate spelled like a variable of `request`, for a
/// local mint that a response can print next to the request's variables.
pub(crate) fn fresh_name_apart(
    base: &str,
    marker: FreshMarker,
    counter: &mut u64,
    avoid: &mut BTreeSet<Name>,
    request: &RequestNames,
) -> String {
    // Invariant: `counter` only grows, so at most |avoid| + |request| + 1 names are tried.
    loop {
        let name = with_fresh_marker(base, marker, *counter);
        *counter += 1;
        if !request.spells(&name) && avoid.insert(name.as_str().into()) {
            return name;
        }
    }
}

/// The counter of one request (an execution, a search, a proof, or a sequence of steps a
/// caller treats as one), and the spellings of the request's variables.
///
/// Every name a rewrite introduces into a state, and every claim variable a proof renames, is
/// minted by [`FreshCounter::mint`], which takes the next value of one counter that only grows:
/// two mints of a request differ in their counter, so no name is reused along a path, even
/// after its first variable left the state. A candidate spelled like a variable of the request
/// is skipped, so no mint prints like a name of the request, free or bound. Requests built
/// from the same patterns mint the same names.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct FreshCounter {
    next: u64,
    request: RequestNames,
}

impl FreshCounter {
    /// The counter of a request whose patterns are `patterns`: every variable of them, free or
    /// bound, is a name of the request.
    pub fn for_request(patterns: &[&Pattern]) -> Self {
        Self::for_request_names(RequestNames::of(patterns))
    }

    /// The counter of a request with the given names.
    pub fn for_request_names(request: RequestNames) -> Self {
        Self { next: 0, request }
    }

    /// The next value of the counter: how many values the request has used, so a caller can
    /// tell whether a step minted a name.
    pub fn next_index(&self) -> u64 {
        self.next
    }

    /// The names of the request.
    pub fn request(&self) -> &RequestNames {
        &self.request
    }

    /// The first `{base}!{marker}{counter}` from this request's counter that is not in `avoid`
    /// and that no variable of the request is spelled as, added to `avoid`.
    pub(crate) fn mint(
        &mut self,
        base: &str,
        marker: FreshMarker,
        avoid: &mut BTreeSet<Name>,
    ) -> String {
        // Invariant: `next` only grows, so at most |avoid| + |request| + 1 names are tried.
        loop {
            let name = with_fresh_marker(base, marker, self.next);
            self.next = self
                .next
                .checked_add(1)
                .expect("a request mints fewer than 2^64 names");
            if !self.request.spells(&name) && avoid.insert(name.as_str().into()) {
                return name;
            }
        }
    }
}

/// `variable` renamed to a `{name}!{counter}` from the request's counter
/// ([`FreshCounter::mint`]) that is not in `names_to_avoid`.
///
/// `name` is the variable's name up to its first `!`: a rule variable renamed apart
/// (`Rule#X!apart3`) or an earlier mint mints from its original name (`X`), since the new
/// counter alone makes the name new.
pub(crate) fn fresh_variable(
    variable: &Variable,
    names_to_avoid: &mut BTreeSet<Name>,
    counter: &mut FreshCounter,
) -> Term {
    let base = variable
        .name
        .split_once('!')
        .map_or(variable.name.as_ref(), |(base, _)| base);
    let name = counter.mint(base, FreshMarker::Rewrite, names_to_avoid);
    Term::variable(variable.with_name(name))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        rule::Predicate,
        term::{CollectionSymbols, MapDefinition, Sort},
    };

    fn variable(name: &str) -> Variable {
        Variable::new(name, Sort::simple("SortS"))
    }

    fn pattern(free: &str, bound: &str) -> Pattern {
        Pattern {
            term: Term::variable(variable(free)),
            constraints: vec![Predicate::Exists(
                variable(bound),
                Box::new(Predicate::True),
            )],
        }
    }

    #[test]
    fn request_names_hold_the_spellings_of_free_and_bound_variables() {
        let names = RequestNames::of(&[&pattern("Ex-hX-b0", "Y")]);
        assert!(names.spells("Ex-hX-b0"));
        assert!(
            names.spells("Ex#X!0"),
            "the mint prints like the request variable"
        );
        assert!(names.spells("Y"));
        assert!(!names.spells("Ex#Y!0"));
        assert!(!names.spells("X"));
    }

    #[test]
    fn a_state_key_identifies_states_up_to_the_names_the_request_did_not_give() {
        let request = RequestNames::of(&[&pattern("X", "B")]);
        let state = |term: &str, left: &str, right: &str| Pattern {
            term: Term::variable(variable(term)),
            constraints: vec![Predicate::Exists(
                variable("Ex#W!9"),
                Box::new(Predicate::Equals(
                    Term::variable(variable(left)),
                    Term::variable(variable(right)),
                )),
            )],
        };
        let key = |term, left, right| request.state_key(&state(term, left, right));
        assert_eq!(
            key("Ex#Y!0", "Ex#Y!0", "Ex#Z!1"),
            key("Ex#Y!4", "Ex#Y!4", "Ex#Z!2"),
            "states that differ in the names of their mints share a key"
        );
        assert_eq!(
            key("Ex#Y!0", "Ex#Y!0", "Ex#W!9"),
            key("Ex#Y!3", "Ex#Y!3", "Ex#W!9"),
            "a bound variable is renamed with its binder"
        );
        assert_ne!(
            key("Ex#Y!0", "Ex#Y!0", "Ex#Z!1"),
            key("Ex#Y!0", "Ex#Z!1", "Ex#Z!1"),
            "the key keeps which positions share a variable"
        );
        assert_ne!(
            key("X", "X", "Ex#Z!1"),
            key("Ex#Y!0", "Ex#Y!0", "Ex#Z!1"),
            "a variable of the request is not a mint"
        );
        assert_eq!(key("X", "X", "Ex#Z!1"), key("X", "X", "Ex#Z!7"));
        let named = Pattern {
            term: Term::variable(variable("X")),
            constraints: Vec::new(),
        };
        assert_eq!(request.state_key(&named), named);
    }

    /// The map `{key |-> value}` over element variables named by `entries`' keys and integer
    /// values.
    fn map(entries: &[(&str, &str)]) -> Term {
        let definition = Arc::new(MapDefinition {
            symbols: CollectionSymbols {
                unit: "unit".into(),
                element: "element".into(),
                concat: "concat".into(),
            },
            key_sort: "SortS".into(),
            value_sort: "SortInt".into(),
            map_sort: "SortMap".into(),
        });
        Term::map(
            definition,
            entries
                .iter()
                .map(|(key, value)| {
                    (
                        Term::variable(variable(key)),
                        Term::domain_value(Sort::simple("SortInt"), *value),
                    )
                })
                .collect(),
            None,
        )
    }

    /// Map entries are stored in the order of their keys, which compares names, so two
    /// renamings of one map store their entries in different orders; the key numbers the
    /// entries in an order that compares the renamed variables by sort only, so both get one
    /// key, while maps that are not renamings of each other keep different keys.
    #[test]
    fn a_state_key_numbers_map_entries_whatever_the_names_of_their_keys() {
        let request = RequestNames::default();
        let key = |entries: &[(&str, &str)]| {
            request.state_key(&Pattern {
                term: map(entries),
                constraints: Vec::new(),
            })
        };
        let first = [
            ("Ex#K!0", "5"),
            ("Ex#K!3", "4"),
            ("Ex#K!6", "3"),
            ("Ex#K!9", "2"),
        ];
        let second = [
            ("Ex#K!0", "5"),
            ("Ex#K!3", "4"),
            ("Ex#K!6", "3"),
            ("Ex#K!10", "2"),
        ];
        assert_eq!(key(&first), key(&second));
        assert_ne!(
            key(&first),
            key(&[
                ("Ex#K!0", "5"),
                ("Ex#K!3", "4"),
                ("Ex#K!6", "3"),
                ("Ex#K!10", "1"),
            ])
        );
    }

    /// Constraints are a conjunction: the key numbers them in an order that does not compare
    /// the renamed names, and sorts them after renaming, so states that list one set of
    /// constraints in different orders, under different names, share a key.
    #[test]
    fn a_state_key_does_not_depend_on_the_order_of_constraints() {
        let request = RequestNames::default();
        let state = |first: &str, second: &str, swap: bool| {
            let mut constraints = vec![
                Predicate::Equals(
                    Term::variable(variable(first)),
                    Term::domain_value(Sort::simple("SortInt"), "1"),
                ),
                Predicate::Ceil(Term::variable(variable(second))),
            ];
            if swap {
                constraints.reverse();
            }
            Pattern {
                term: Term::variable(variable("Ex#Z!7")),
                constraints,
            }
        };
        assert_eq!(
            request.state_key(&state("Ex#A!1", "Ex#B!2", false)),
            request.state_key(&state("Ex#B!5", "Ex#A!4", true))
        );
        assert_ne!(
            request.state_key(&state("Ex#A!1", "Ex#B!2", false)),
            request.state_key(&state("Ex#A!1", "Ex#A!1", false))
        );
    }

    /// A solution's key renames the variables the request does not name in the bound values
    /// and the constraints together, and keeps the request's names.
    #[test]
    fn a_solution_key_identifies_solutions_up_to_the_names_the_request_did_not_give() {
        let request = RequestNames::of(&[&pattern("VarV", "B")]);
        let solution = |value: &str| {
            let substitution =
                Substitution::from([(variable("VarV"), Term::variable(variable(value)))]);
            let constraints = vec![Predicate::Ceil(Term::variable(variable(value)))];
            request.solution_key(&substitution, &constraints)
        };
        assert_eq!(solution("Ex#X!0"), solution("Ex#X!1"));
        assert_ne!(solution("Ex#X!0"), solution("VarV"));
        let (substitution, _) = solution("Ex#X!0");
        assert!(substitution.contains_key(&variable("VarV")));
    }

    #[test]
    fn a_request_counter_never_reuses_a_value() {
        let mut counter = FreshCounter::for_request(&[]);
        let mut first = BTreeSet::new();
        let mut second = BTreeSet::new();
        assert_eq!(counter.mint("X", FreshMarker::Rewrite, &mut first), "X!0");
        // Another avoid set, as in a later step whose state no longer has `X!0`.
        assert_eq!(counter.mint("X", FreshMarker::Rewrite, &mut second), "X!1");
        assert_eq!(
            counter.mint("Y", FreshMarker::Claim, &mut second),
            "Y!claim2"
        );
    }

    #[test]
    fn a_request_counter_skips_the_spellings_of_the_request() {
        let mut counter =
            FreshCounter::for_request(&[&pattern("Ex-hX-b0", "Ex-hX-b1"), &pattern("Z", "Y")]);
        let mut avoid = BTreeSet::new();
        assert_eq!(
            counter.mint("Ex#X", FreshMarker::Rewrite, &mut avoid),
            "Ex#X!2"
        );
        assert_eq!(
            counter.mint("Ex#Y", FreshMarker::Rewrite, &mut avoid),
            "Ex#Y!3"
        );
    }
}
