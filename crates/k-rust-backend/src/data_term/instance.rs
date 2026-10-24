//! The bounded search for a ground instance of an unjoined pair on which the definition's
//! equations give two different constructor values (the parent module's "Findings: genuine or
//! undecided").
//!
//! Each variable of the pair's overlap, reducts and conditions ([`UnjoinedPair::overlap`],
//! [`UnjoinedPair::sides`], [`UnjoinedPair::conditions`]) gets a few small ground terms of its
//! sort ([`Search::candidates`]): domain values (`0`, `1`, `-1` for an integer sort, `false` and
//! `true`, `""` and `"a"` for a string sort), nullary free constructors, empty and one-element
//! collections, free-constructor applications over such terms, and injections of a subsort's
//! terms. The assignments are tried in a fixed order, at most [`INSTANCES`] per pair. One is an
//! instance when, under it:
//!
//! - the overlap's instance is defined: every map and set in it holds distinct keys and
//!   elements (a left-hand side matches only a defined subject);
//! - both equations apply there, each at its own redex (the overlap's instance, and for an
//!   inner pair its subterm at the pair's position): its left-hand side matches the redex, its
//!   `requires` evaluates to `true`, it has no `ensures`, and no executable equation of the same
//!   head in a group of higher priority (`priority`, `owise` the lowest) matches the redex with
//!   its `requires` true or undecided, since every equation holds only under that priority
//!   antecedent (`docs/compatibility.md`, the priority reading of `M_NF`);
//! - each reduct evaluates, unconditionally and without a stop, to a ground term built only from
//!   free constructors, injections, domain values and rest-free collections with distinct keys
//!   and elements;
//! - the two values are *surely distinct* ([`surely_distinct`]): distinct in every model in
//!   which the definition's constructor declarations, the sort injections' injectivity and the
//!   builtin hooks hold. Two terms that differ only by the source sorts of injections, or that
//!   an overload equation may identify, are not;
//! - no evaluation noted an implementation-chosen value or a contradicted claim.
//!
//! Each equation applies at its redex, so the redex equals its reduct in every model, and the
//! evaluation of a reduct applies equations (respecting their priorities) and hooks only, so
//! the reduct equals its value in every model. The overlap's instance therefore equals both
//! values, which no model keeps apart from each other: no model satisfies the definition. The
//! search decides nothing when it finds no instance: the finding stays undecided.

use std::collections::BTreeSet;

use rustc_hash::FxHashMap;

use crate::{
    condition::Condition,
    definition::BackendDefinition,
    diagnostic,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::Predicate,
    rule::{Concreteness, ConstraintKind, RewriteRule, term_index},
    simplify::{SimplificationOptions, simplify, simplify_predicate_with_solver},
    smt::NoSolver,
    substitution::{Substitution, substitute},
    term::{CollectionMetadata, HeadRole, Sort, SortNode, Term, TermKind, Variable},
};

use crate::confluence::UnjoinedPair;

/// The assignments tried per pair.
const INSTANCES: usize = 81;

/// The ground terms of one sort the search tries for a variable.
const CANDIDATES: usize = 3;

/// How deep a candidate's free-constructor applications nest.
const DEPTH: usize = 2;

/// The polls (`stop::check`) one evaluation of the search may make: an evaluation that needs
/// more decides nothing, which loses an instance at worst.
const EVALUATION_POLLS: u64 = 200_000;

/// The equation iterations one evaluation may take.
const EVALUATION_ITERATIONS: usize = 256;

/// A ground instance of an unjoined pair's overlap on which the two reducts evaluate to two
/// different constructor terms (the parent module's "Findings: genuine or undecided").
#[derive(Clone, Debug)]
pub struct GroundInstance {
    /// Each variable of the overlap, the reducts and the conditions, with its ground value, in
    /// order of their names.
    pub assignment: Vec<(Variable, Term)>,
    /// The overlap under the assignment: the ground term both equations rewrite.
    pub overlap: Term,
    /// What each reduct evaluates to, in the order of [`UnjoinedPair::sides`] (the first
    /// equation's, then the second's).
    pub values: (Term, Term),
}

/// The search over one definition, with the candidates of each sort computed once.
pub(super) struct Search<'d> {
    definition: &'d BackendDefinition,
    candidates: FxHashMap<(Sort, usize), Vec<Term>>,
}

impl<'d> Search<'d> {
    pub(super) fn new(definition: &'d BackendDefinition) -> Self {
        Self {
            definition,
            candidates: FxHashMap::default(),
        }
    }

    /// A ground instance of `pair` (see the module documentation), or `None` when the pair has
    /// no overlap, no reducts or unsimplified conditions, or no assignment tried is one.
    pub(super) fn ground_instance(&mut self, pair: &UnjoinedPair) -> Option<GroundInstance> {
        let overlap = pair.overlap.as_ref()?;
        let (Some(first), Some(second)) = pair.sides.as_ref()? else {
            return None;
        };
        let conditions = pair.conditions.as_ref()?;
        // An `ensures` may make a step's result `\bottom` at the instance: not read here.
        if !pair.first.ensures.is_empty() || !pair.second.ensures.is_empty() {
            return None;
        }
        let mut variables = BTreeSet::new();
        for term in [overlap, first, second] {
            variables.extend(term.attributes().variables.iter().cloned());
        }
        variables.extend(conditions.free_variables());
        let variables = variables.into_iter().collect::<Vec<_>>();
        let mut choices = Vec::with_capacity(variables.len());
        for variable in &variables {
            let candidates = self.candidates(variable.sort, DEPTH);
            if candidates.is_empty() {
                return None;
            }
            choices.push(candidates);
        }
        crate::stop::detached(|| {
            let mut digits = vec![0_usize; choices.len()];
            for _ in 0..INSTANCES {
                let assignment = variables
                    .iter()
                    .zip(&choices)
                    .zip(&digits)
                    .map(|((variable, candidates), digit)| {
                        (variable.clone(), candidates[*digit].clone())
                    })
                    .collect::<Vec<_>>();
                if let Some(instance) =
                    self.try_assignment(pair, &assignment, overlap, (first, second), conditions)
                {
                    return Some(instance);
                }
                // The next assignment in mixed radix, the last variable fastest.
                let mut position = digits.len();
                loop {
                    if position == 0 {
                        return None;
                    }
                    position -= 1;
                    digits[position] += 1;
                    if digits[position] < choices[position].len() {
                        break;
                    }
                    digits[position] = 0;
                }
            }
            None
        })
    }

    fn try_assignment(
        &self,
        pair: &UnjoinedPair,
        assignment: &[(Variable, Term)],
        overlap: &Term,
        (first, second): (&Term, &Term),
        conditions: &Predicate,
    ) -> Option<GroundInstance> {
        let substitution = assignment.iter().cloned().collect::<Substitution>();
        let instance = substitute(overlap, &substitution);
        if !well_formed_collections(self.definition, &instance) {
            return None;
        }
        // Every comparison the evaluation makes between the instance's data terms (a map lookup,
        // `==K`, a match against a constant of the equations) reads them as distinct or equal;
        // only terms kept apart in every model of the stated premises may be read as distinct.
        let mut read = vec![
            instance.clone(),
            substitute(first, &substitution),
            substitute(second, &substitution),
        ];
        conditions.visit_terms(&mut |term| read.push(substitute(term, &substitution)));
        let fixed = self.matched_constants(pair, &read);
        if !self.apart(&read, &fixed) {
            return None;
        }
        let (values, diagnostics) = diagnostic::collect(|| {
            if !self.holds(conditions, &substitution) {
                return None;
            }
            if !self.applies(&pair.first, &instance) {
                return None;
            }
            let inner = inner_redex(&pair.first.lhs, &instance, &pair.position)?;
            // `second` applies at the redex, or under an injection at a position of a greater
            // sort.
            let applies = self.applies(&pair.second, &inner)
                || matches!(inner.kind(), TermKind::Injection { term, .. }
                    if self.applies(&pair.second, term));
            if !applies {
                return None;
            }
            let left = self.value(&substitute(first, &substitution))?;
            let right = self.value(&substitute(second, &substitution))?;
            Some((left, right))
        });
        let (left, right) = values?;
        if !surely_distinct(self.definition, &left, &right)
            || !self.apart(&[left.clone(), right.clone()], &[])
            || diagnostics
                .iter()
                .any(diagnostic::BackendDiagnostic::is_path_fact)
        {
            return None;
        }
        Some(GroundInstance {
            assignment: assignment.to_vec(),
            overlap: instance,
            values: (left, right),
        })
    }

    /// Whether every two different ground data terms of one sort that the search reads are
    /// surely distinct ([`surely_distinct`]): any two subterms of `terms` (the instance, its
    /// reducts and conditions, or the values), and a subterm of `terms` beside a constant of
    /// `fixed` (the ground data subterms of the left-hand sides and `requires` whose matching the
    /// search reads, [`Self::matched_constants`]). Otherwise some model of the premises
    /// identifies them, and a step that told them apart (a map lookup, `==K`, `in_keys`, a match
    /// refuted by a constant) proves nothing in that model. Map keys and set elements obey the
    /// same rule ([`well_formed_collections`]).
    fn apart(&self, terms: &[Term], fixed: &[Term]) -> bool {
        let read = self.ground_data(terms);
        let constants = self.ground_data(fixed);
        read.iter().all(|(sort, terms)| {
            terms.iter().enumerate().all(|(index, left)| {
                terms[index + 1..]
                    .iter()
                    .chain(constants.get(sort).into_iter().flatten())
                    .all(|right| left == right || surely_distinct(self.definition, left, right))
            })
        })
    }

    /// The ground data subterms of `terms` (built from free constructors, injections, domain
    /// values and rest-free collections), by sort, each once.
    fn ground_data(&self, terms: &[Term]) -> FxHashMap<Sort, Vec<Term>> {
        let mut by_sort: FxHashMap<Sort, Vec<Term>> = FxHashMap::default();
        let mut pending = terms.to_vec();
        while let Some(term) = pending.pop() {
            pending.extend(subterms(&term));
            if term.attributes().variables.is_empty()
                && self.definition.built_from_data(&term, &BTreeSet::new())
            {
                let seen = by_sort.entry(term.sort()).or_default();
                if !seen.contains(&term) {
                    seen.push(term);
                }
            }
        }
        by_sort
    }

    /// The left-hand sides and `requires` of the equations whose matching the search reads: the
    /// pair's two, every executable equation of their heads (a higher-priority one is read as
    /// refuted when its match fails), and every executable equation of each symbol applied in
    /// `read` (the evaluation of the reducts tries them).
    fn matched_constants(&self, pair: &UnjoinedPair, read: &[Term]) -> Vec<Term> {
        let mut indexes = vec![term_index(&pair.first.lhs), term_index(&pair.second.lhs)];
        let mut pending = read.to_vec();
        while let Some(term) = pending.pop() {
            pending.extend(subterms(&term));
            if let TermKind::Application { .. } = term.kind() {
                let index = term_index(&term);
                if !indexes.contains(&index) {
                    indexes.push(index);
                }
            }
        }
        let mut constants = Vec::new();
        for index in &indexes {
            let Some(groups) = self.definition.function_theory().get(index) else {
                continue;
            };
            for rule in groups.values().flatten() {
                constants.push(rule.lhs.clone());
                rule.requires.iter().for_each(|predicate| {
                    predicate.visit_terms(&mut |term| constants.push(term.clone()))
                });
            }
        }
        constants
    }

    /// Whether `conditions` under `substitution` evaluates to `true`, each term's definedness
    /// stated.
    fn holds(&self, conditions: &Predicate, substitution: &Substitution) -> bool {
        *conditions == Predicate::True
            || self.truth(&Condition::new(vec![conditions.clone()]), substitution) == Some(true)
    }

    /// What `condition` under `substitution` evaluates to, each term's definedness stated:
    /// `Some(true)` or `Some(false)` when it simplifies to `\top` or `\bottom`, `None` otherwise.
    fn truth(&self, condition: &Condition, substitution: &Substitution) -> Option<bool> {
        if condition.is_empty() {
            return Some(true);
        }
        let instance = condition.instantiate(substitution);
        let (decided, stops) = budgeted(|| {
            let Ok(predicates) = instance.with_definedness(self.definition, &[]) else {
                return None;
            };
            let options = SimplificationOptions {
                max_iterations: EVALUATION_ITERATIONS,
                ..SimplificationOptions::default()
            };
            match simplify_predicate_with_solver(
                self.definition,
                &Predicate::And(predicates.into()),
                &[],
                options,
                &NoSolver,
            ) {
                Ok(Ok(Predicate::True)) => Some(true),
                Ok(Ok(Predicate::False)) => Some(false),
                _ => None,
            }
        });
        decided.filter(|_| !stops.any())
    }

    /// Whether `rule` applies at the ground term `redex`: its left-hand side matches, its
    /// `requires` evaluates to `true`, and no executable equation of the same head in a group of
    /// higher priority matches with its `requires` true or undecided.
    fn applies(&self, rule: &RewriteRule, redex: &Term) -> bool {
        if self.matches(rule, redex) != Some(true) {
            return false;
        }
        let Some(groups) = self
            .definition
            .function_theory()
            .get(&term_index(&rule.lhs))
        else {
            return false;
        };
        groups
            .range(..rule.attributes.priority)
            .flat_map(|(_, rules)| rules)
            .filter(|other| other.attributes.executable && !symbolic(other))
            .all(|other| self.matches(other, redex) == Some(false))
    }

    /// Whether `rule`'s left-hand side matches `redex` with its `requires` true (`Some(true)`),
    /// does not match or matches with its `requires` false (`Some(false)`), or neither is decided.
    fn matches(&self, rule: &RewriteRule, redex: &Term) -> Option<bool> {
        match match_terms_in_definition(MatchMode::Evaluate, self.definition, &rule.lhs, redex) {
            MatchResult::Failed(_) => Some(false),
            MatchResult::Success(substitution) => self.truth(&rule.requires, &substitution),
            MatchResult::Indeterminate { .. } | MatchResult::Undecided(_) => None,
        }
    }

    /// The value `term` evaluates to, when it evaluates unconditionally, within the budget, to
    /// a ground term built only from free constructors, injections, domain values and rest-free
    /// collections with distinct keys and elements.
    fn value(&self, term: &Term) -> Option<Term> {
        let (value, stops) = budgeted(|| {
            let options = SimplificationOptions {
                max_iterations: EVALUATION_ITERATIONS,
                ..SimplificationOptions::default()
            };
            match simplify(self.definition, term, options) {
                Ok(Ok(simplified))
                    if simplified.is_unconditional()
                        && simplified.exhausted.is_none()
                        && simplified.undefined_term.is_none() =>
                {
                    Some(simplified.term)
                }
                _ => None,
            }
        });
        let value = value.filter(|_| !stops.any())?;
        (value.attributes().variables.is_empty()
            && self.definition.built_from_data(&value, &BTreeSet::new()))
        .then_some(value)
    }

    /// At most [`CANDIDATES`] small ground terms of `sort`, free constructors nested at most
    /// `depth` deep, in a fixed order: domain values and nullary symbols first.
    fn candidates(&mut self, sort: Sort, depth: usize) -> Vec<Term> {
        if let Some(found) = self.candidates.get(&(sort, depth)) {
            return found.clone();
        }
        // A cycle through a sort (a constructor whose argument is its own sort) reads the entry
        // as empty while it is computed.
        self.candidates.insert((sort, depth), Vec::new());
        let found = self.compute_candidates(sort, depth);
        self.candidates.insert((sort, depth), found.clone());
        found
    }

    fn compute_candidates(&mut self, sort: Sort, depth: usize) -> Vec<Term> {
        let SortNode::Application { name, arguments } = sort.node() else {
            return Vec::new();
        };
        if !arguments.is_empty() {
            return Vec::new();
        }
        let definition = self.definition;
        let mut found = Vec::new();
        let push = |found: &mut Vec<Term>, term: Term| {
            if found.len() < CANDIDATES && !found.contains(&term) {
                found.push(term);
            }
        };
        if let Some(info) = definition.sorts().get(name) {
            let texts: &[&str] = match info.hook.as_deref() {
                Some("INT.Int") => &["0", "1", "-1"],
                Some("BOOL.Bool") => &["false", "true"],
                Some("STRING.String") => &["", "a"],
                _ => &[],
            };
            for text in texts {
                if let Ok(term) = definition.domain_value(sort, *text) {
                    push(&mut found, term);
                }
            }
        }
        // The definition's own constructors before K's internal ones (`#`-labelled, such as
        // `#KConfigValue`), which a reader of the instance would not recognize.
        let mut constructors = definition
            .symbols()
            .values()
            .filter(|symbol| {
                symbol.result_sort == sort
                    && symbol.sort_variables.is_empty()
                    && symbol.attributes.head_role() == HeadRole::FreeConstructor
            })
            .cloned()
            .collect::<Vec<_>>();
        constructors.sort_by_key(|symbol| symbol.name.starts_with("Lbl'Hash'"));
        for symbol in constructors
            .iter()
            .filter(|symbol| symbol.argument_sorts.is_empty())
        {
            push(
                &mut found,
                Term::application(symbol.clone(), Vec::<Sort>::new(), Vec::new()),
            );
        }
        let collection = definition.symbols().values().find_map(|symbol| {
            let metadata = symbol.attributes.collection.as_ref()?;
            let collection_sort = match metadata {
                CollectionMetadata::Map(map) => &map.map_sort,
                CollectionMetadata::List(list) | CollectionMetadata::Set(list) => &list.list_sort,
            };
            (collection_sort == name).then(|| metadata.clone())
        });
        if let Some(metadata) = &collection {
            push(&mut found, empty_collection(metadata));
        }
        if depth > 0 {
            // Each constructor over its arguments' first candidates, then, while room is
            // left, over their other candidates in mixed radix (the last argument fastest), so
            // that a sort with one constructor (`wrap(Int)`) still has several terms.
            let applied = constructors
                .iter()
                .filter(|symbol| !symbol.argument_sorts.is_empty())
                .filter_map(|symbol| {
                    let choices = symbol
                        .argument_sorts
                        .iter()
                        .map(|argument| self.candidates(*argument, depth - 1))
                        .collect::<Vec<_>>();
                    choices
                        .iter()
                        .all(|choice| !choice.is_empty())
                        .then_some((symbol, choices))
                })
                .collect::<Vec<_>>();
            for round in 0..CANDIDATES {
                for (symbol, choices) in &applied {
                    if found.len() >= CANDIDATES {
                        break;
                    }
                    let mut index = round;
                    let mut arguments = vec![None; choices.len()];
                    for (position, choice) in choices.iter().enumerate().rev() {
                        arguments[position] = Some(choice[index % choice.len()].clone());
                        index /= choice.len();
                    }
                    if round > 0 && index > 0 {
                        // Every combination was tried.
                        continue;
                    }
                    push(
                        &mut found,
                        Term::application(
                            (*symbol).clone(),
                            Vec::<Sort>::new(),
                            arguments.into_iter().flatten().collect(),
                        ),
                    );
                }
            }
            if let Some(metadata) = &collection
                && let Some(single) = self.singleton_collection(metadata, depth - 1)
            {
                push(&mut found, single);
            }
        }
        if found.len() < CANDIDATES {
            let below = definition
                .sort_graph()
                .closures()
                .find(|(above, _)| *above.sort() == sort)
                .map(|(_, below)| {
                    below
                        .iter()
                        .map(|closed| *closed.sort())
                        .filter(|below| *below != sort)
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();
            for subsort in below {
                if found.len() >= CANDIDATES {
                    break;
                }
                for candidate in self.candidates(subsort, depth) {
                    push(&mut found, Term::injection(subsort, sort, candidate));
                }
            }
        }
        found
    }

    /// A one-element (one-entry) collection of the first candidates of its element sorts.
    fn singleton_collection(
        &mut self,
        metadata: &CollectionMetadata,
        depth: usize,
    ) -> Option<Term> {
        Some(match metadata {
            CollectionMetadata::Map(map) => {
                let key = self.candidates(map.key_sort, depth).first()?.clone();
                let value = self.candidates(map.value_sort, depth).first()?.clone();
                Term::map(map.clone(), vec![(key, value)], None)
            }
            CollectionMetadata::List(list) => {
                let element = self.candidates(list.element_sort, depth).first()?.clone();
                Term::list(list.clone(), vec![element], None)
            }
            CollectionMetadata::Set(set) => {
                let element = self.candidates(set.element_sort, depth).first()?.clone();
                Term::set(set.clone(), vec![element], None)
            }
        })
    }
}

/// Whether `rule` holds only on symbolic instances, so it is never a step on a ground term.
fn symbolic(rule: &RewriteRule) -> bool {
    match &rule.attributes.concreteness {
        Concreteness::Unconstrained => false,
        Concreteness::All(kind) => *kind == ConstraintKind::Symbolic,
        Concreteness::Some(constraints) => constraints
            .values()
            .any(|kind| *kind == ConstraintKind::Symbolic),
    }
}

/// Whether every map and set in `term` holds keys and elements that are pairwise surely
/// distinct ([`surely_distinct`], the same reading as the values'): otherwise some model of the
/// premises identifies two of them, the collection is `\bottom` there, and no equation applies at
/// it.
fn well_formed_collections(definition: &BackendDefinition, term: &Term) -> bool {
    let distinct = |items: &[&Term]| {
        items.iter().enumerate().all(|(index, left)| {
            items[index + 1..]
                .iter()
                .all(|right| surely_distinct(definition, left, right))
        })
    };
    let collections_apart = match term.kind() {
        TermKind::Map { entries, .. } => {
            distinct(&entries.iter().map(|(key, _)| key).collect::<Vec<_>>())
        }
        TermKind::Set { elements, .. } => distinct(&elements.iter().collect::<Vec<_>>()),
        _ => true,
    };
    collections_apart
        && subterms(term)
            .iter()
            .all(|subterm| well_formed_collections(definition, subterm))
}

/// The immediate subterms of `term`.
fn subterms(term: &Term) -> Vec<Term> {
    match term.kind() {
        TermKind::Application { arguments, .. } => arguments.clone(),
        TermKind::Injection { term, .. } => vec![term.clone()],
        TermKind::And(left, right) => vec![left.clone(), right.clone()],
        TermKind::Map { entries, rest, .. } => entries
            .iter()
            .flat_map(|(key, value)| [key.clone(), value.clone()])
            .chain(rest.clone())
            .collect(),
        TermKind::List { heads, rest, .. } => heads
            .iter()
            .cloned()
            .chain(rest.iter().flat_map(|(middle, tails)| {
                std::iter::once(middle.clone()).chain(tails.iter().cloned())
            }))
            .collect(),
        TermKind::Set { elements, rest, .. } => {
            elements.iter().cloned().chain(rest.clone()).collect()
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => Vec::new(),
    }
}

/// The subterm of `instance`, the overlap's instance of `lhs`, at `position` (argument indexes
/// in `lhs`, an `\and`'s conjuncts counted as its arguments 0 and 1, as `UnjoinedPair::position`
/// counts them). `None` when the path enters a collection, or `instance` does not have `lhs`'s
/// shape along it: the redex is then not located, and no instance is claimed.
fn inner_redex(lhs: &Term, instance: &Term, position: &[usize]) -> Option<Term> {
    let (mut pattern, mut term) = (lhs.clone(), instance.clone());
    for index in position {
        if let TermKind::And(left, right) = pattern.kind() {
            // The instance holds one term for both conjuncts.
            pattern = (*[left, right].get(*index)?).clone();
            continue;
        }
        let next = match (pattern.kind(), term.kind()) {
            (
                TermKind::Application {
                    symbol, arguments, ..
                },
                TermKind::Application {
                    symbol: found,
                    arguments: held,
                    ..
                },
            ) if symbol.name == found.name && arguments.len() == held.len() => {
                (arguments.get(*index)?.clone(), held.get(*index)?.clone())
            }
            (TermKind::Injection { term: inner, .. }, TermKind::Injection { term: held, .. })
                if *index == 0 =>
            {
                (inner.clone(), held.clone())
            }
            _ => return None,
        };
        (pattern, term) = next;
    }
    Some(term)
}

/// Whether the ground terms `left` and `right`, built from free constructors, injections,
/// domain values and collections, are distinct in every model in which the constructor
/// declarations (distinct constructors of one sort differ, each constructor is injective), the
/// injectivity of each sort injection and the builtin hooks hold. Conservative: two injections
/// from different source sorts are not separated by any axiom (an overload equation may even
/// identify them), nor are an injection and a constructor of the target sort, nor maps and sets
/// whose elements would have to be paired up; such terms are not counted distinct.
pub(super) fn surely_distinct(definition: &BackendDefinition, left: &Term, right: &Term) -> bool {
    match (left.kind(), right.kind()) {
        // Distinct values of a hooked sort are distinct builtin values; a sort with domain
        // values but no hook (a token sort) states no such axiom.
        (TermKind::DomainValue { .. }, TermKind::DomainValue { .. }) => {
            left.sort() == right.sort()
                && left != right
                && crate::confluence::symbols::fixed_carrier(definition, &left.sort())
        }
        (
            TermKind::Injection {
                source: left_source,
                term: left_term,
                ..
            },
            TermKind::Injection {
                source: right_source,
                term: right_term,
                ..
            },
        ) => left_source == right_source && surely_distinct(definition, left_term, right_term),
        (
            TermKind::Application {
                symbol: left_symbol,
                arguments: left_arguments,
                ..
            },
            TermKind::Application {
                symbol: right_symbol,
                arguments: right_arguments,
                ..
            },
        ) => {
            let constructor = |symbol: &crate::term::Symbol| {
                symbol.attributes.head_role() == HeadRole::FreeConstructor
            };
            if !constructor(left_symbol) || !constructor(right_symbol) {
                return false;
            }
            if left_symbol.name != right_symbol.name {
                // Two free constructors of one sort: no confusion. An overloaded one may be
                // identified with another through its family's overload equations only under
                // an injection, which the case above does not separate.
                return left_symbol.result_sort == right_symbol.result_sort
                    && !definition.overloads().is_overloaded(&left_symbol.name)
                    && !definition.overloads().is_overloaded(&right_symbol.name);
            }
            left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments)
                    .any(|(left, right)| surely_distinct(definition, left, right))
        }
        (
            TermKind::List {
                definition: left_list,
                heads: left_heads,
                rest: None,
            },
            TermKind::List {
                definition: right_list,
                heads: right_heads,
                rest: None,
            },
        ) => {
            left_list == right_list
                && (left_heads.len() != right_heads.len()
                    || left_heads
                        .iter()
                        .zip(right_heads.iter())
                        .any(|(left, right)| surely_distinct(definition, left, right)))
        }
        _ => false,
    }
}

/// The empty collection of `metadata`'s sort.
fn empty_collection(metadata: &CollectionMetadata) -> Term {
    match metadata {
        CollectionMetadata::Map(map) => Term::map(map.clone(), Vec::new(), None),
        CollectionMetadata::List(list) => Term::list(list.clone(), Vec::new(), None),
        CollectionMetadata::Set(set) => Term::set(set.clone(), Vec::new(), None),
    }
}

/// Run `work` under the budget of [`EVALUATION_POLLS`] polls.
fn budgeted<T>(work: impl FnOnce() -> T) -> (T, crate::stop::PollBudgetRecord) {
    crate::stop::with_poll_budget(
        EVALUATION_POLLS,
        crate::timeout::StepTimeoutMode::Manual(std::time::Duration::from_secs(1)),
        work,
    )
}
