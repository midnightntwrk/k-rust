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
//! - the pair's conditions evaluate to `true` (they are the conjunction of both `requires` at
//!   the overlap, simplified by the check with every claim withheld, so `true` here means both
//!   `requires` hold at the instance);
//! - each reduct evaluates, unconditionally and without a stop, to a ground term built only from
//!   free constructors, injections, domain values and rest-free collections with distinct keys
//!   and elements;
//! - the two values differ;
//! - no evaluation noted an implementation-chosen value or a contradicted claim.
//!
//! The reducts are one equation step each from the overlap's instance and their evaluation
//! applies equations and hooks only, so the definition states that the instance equals both
//! values. The search decides nothing when it finds no instance: the finding stays undecided.

use std::collections::BTreeSet;

use rustc_hash::FxHashMap;

use crate::{
    condition::Condition,
    definition::BackendDefinition,
    diagnostic,
    rule::Predicate,
    simplify::{SimplificationOptions, simplify, simplify_predicate_with_solver},
    smt::NoSolver,
    substitution::{Substitution, substitute},
    term::{CollectionMetadata, HeadRole, Sort, SortNode, Term, Variable},
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
                    self.try_assignment(&assignment, overlap, (first, second), conditions)
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
        assignment: &[(Variable, Term)],
        overlap: &Term,
        (first, second): (&Term, &Term),
        conditions: &Predicate,
    ) -> Option<GroundInstance> {
        let substitution = assignment.iter().cloned().collect::<Substitution>();
        let (values, diagnostics) = diagnostic::collect(|| {
            if !self.holds(conditions, &substitution) {
                return None;
            }
            let left = self.value(&substitute(first, &substitution))?;
            let right = self.value(&substitute(second, &substitution))?;
            Some((left, right))
        });
        let (left, right) = values?;
        if left == right
            || diagnostics
                .iter()
                .any(diagnostic::BackendDiagnostic::is_path_fact)
        {
            return None;
        }
        Some(GroundInstance {
            assignment: assignment.to_vec(),
            overlap: substitute(overlap, &substitution),
            values: (left, right),
        })
    }

    /// Whether `conditions` under `substitution` evaluates to `true`, each term's definedness
    /// stated.
    fn holds(&self, conditions: &Predicate, substitution: &Substitution) -> bool {
        if *conditions == Predicate::True {
            return true;
        }
        let instance = Condition::new(vec![conditions.clone()]).instantiate(substitution);
        let (decided, _) = budgeted(|| {
            let Ok(predicates) = instance.with_definedness(self.definition, &[]) else {
                return false;
            };
            let options = SimplificationOptions {
                max_iterations: EVALUATION_ITERATIONS,
                ..SimplificationOptions::default()
            };
            matches!(
                simplify_predicate_with_solver(
                    self.definition,
                    &Predicate::And(predicates.into()),
                    &[],
                    options,
                    &NoSolver,
                ),
                Ok(Ok(Predicate::True))
            )
        });
        decided
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
        let constructors = definition
            .symbols()
            .values()
            .filter(|symbol| {
                symbol.result_sort == sort
                    && symbol.sort_variables.is_empty()
                    && symbol.attributes.head_role() == HeadRole::FreeConstructor
            })
            .cloned()
            .collect::<Vec<_>>();
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
            for symbol in constructors
                .iter()
                .filter(|symbol| !symbol.argument_sorts.is_empty())
            {
                if found.len() >= CANDIDATES {
                    break;
                }
                let mut arguments = Vec::with_capacity(symbol.argument_sorts.len());
                for argument in &symbol.argument_sorts {
                    match self.candidates(*argument, depth - 1).first() {
                        Some(candidate) => arguments.push(candidate.clone()),
                        None => break,
                    }
                }
                if arguments.len() == symbol.argument_sorts.len() {
                    push(
                        &mut found,
                        Term::application(symbol.clone(), Vec::<Sort>::new(), arguments),
                    );
                }
            }
            if let Some(metadata) = &collection {
                if let Some(single) = self.singleton_collection(metadata, depth - 1) {
                    push(&mut found, single);
                }
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
