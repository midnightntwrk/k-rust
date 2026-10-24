//! The bounded search for a ground input with two results: an instance of an unjoined pair's
//! overlap at which both equations apply and whose two reducts evaluate to two different normal
//! forms, or to a normal form and an undefined value (the parent module's "Findings: genuine or
//! undecided").
//!
//! Each variable of the pair's overlap, reducts and conditions ([`UnjoinedPair::overlap`],
//! [`UnjoinedPair::sides`], [`UnjoinedPair::conditions`]) gets a few small ground terms of its
//! sort ([`Search::candidates`]): domain values (`0`, `1`, `-1` for an integer sort, `false` and
//! `true`, `""` and `"a"` for a string sort and for a bytes sort), nullary free constructors,
//! empty and one-element collections, free-constructor applications over such terms, and
//! injections of a subsort's terms, all normal forms. The assignments are tried in a fixed order,
//! at most [`INSTANCES`] per pair. One is an instance when, under it:
//!
//! - the overlap's instance is built from normal forms: every map and set in it is keyed by
//!   distinct normal forms (no repeated key or element, k-rust's internal normal form compared);
//! - both equations apply there by the evaluator's own rule, each at its own redex (the
//!   overlap's instance, and for an inner pair its subterm at the pair's position): its
//!   left-hand side matches the redex, its `requires` evaluates to `true`, it has no `ensures`,
//!   and no executable equation of the same head in a group of higher priority (`priority`,
//!   `owise` the lowest) matches the redex with its `requires` true or undecided;
//! - each reduct evaluates, unconditionally and without a stop, to a ground term that is
//!   *defined* or *undefined* (below);
//! - the two values are both defined and differ (on k-rust's internal normal form, whose
//!   injections compose), or exactly one of them is undefined;
//! - no evaluation noted an implementation-chosen value or a contradicted claim.
//!
//! # Stuck applications
//!
//! An application is *stuck* when its arguments are defined and every equation and lemma at its
//! index and at the bare-variable index (every priority, `owise` and overload equations, and
//! also the axioms the evaluator does not apply to it: `symbolic` equations and
//! `simplification` lemmas) fails to match it or matches with its `requires` evaluating to
//! `false`, and no `non-executable` equation or lemma is rooted at its symbol (the load keeps no
//! rule of one to match, so its symbol is left out whole). An axiom that matched would equate the application with another term
//! in every model, and a value `M_NF` already gives against it would say nothing about the pair. What a stuck application is in `M_NF` depends on its
//! symbol's class, read through `confluence::symbols::Class`, which the join reads too
//! (`confluence/join.rs`, rule 3), so a change of that reading moves the search with it:
//!
//! - a *defined* value is built from domain values, injections, free-constructor applications,
//!   rest-free collections with distinct keys and elements, and stuck applications of declared
//!   total functions without a hook or an algebraic axiom (`Class::Total` with
//!   `HeadRole::Function { declared: true, .. }`). Such a stuck application is a normal form of
//!   `M_NF` (`docs/compatibility.md`, "Anywhere rules"), distinct from every other normal form.
//!   A symbol with `assoc`, `comm`, `unit` or `idem` is left out: its axioms are emitted and
//!   never used by the backend, so `M_NF` fails them at every input, and two of its stuck
//!   applications that the axioms equate would say nothing about the pair. Residuals,
//!   `functional` uninterpreted symbols, equation heads and hooked symbols are left out too;
//! - an *undefined* value holds a stuck application whose class makes it `\bottom`
//!   (`Class::stuck_is_bottom`) and is not hooked, a declared partial function without a hook,
//!   reached from the root through free constructors, injections and collection items only, the
//!   other parts of the term defined. It is `\bottom` in `M_NF`. A partial hook's missing value is
//!   left out: `M_NF` gives it the builtin meaning, which the hook's text may leave open;
//! - any other term, for instance a stuck partial application under a stuck total application
//!   or under a hooked symbol, is neither, and gives no instance.
//!
//! Then the input has two different results in `M_NF`, one through each equation: two normal
//! forms, or a normal form and `\bottom`. A term cannot equal both, so `M_NF` is not a model of
//! the definition (the parent module, "What a data term denotes"). The evaluator does not reduce
//! a stuck partial application to `\bottom` (`docs/compatibility.md`, "Anywhere rules"), but its
//! two results still differ, so k-rust's result for that input depends on the order in which it
//! tries the equations. Two undefined values are not an instance. This is no claim about every
//! model of the definition: KORE keeps, for instance, injections from different source sorts
//! apart by no axiom, and a model may give a partial function a value where no equation does.
//! The search decides nothing when it finds no instance: the finding stays undecided.

use std::collections::BTreeSet;

use k_rust_kore::kore::ast::Pattern as KorePattern;
use rustc_hash::FxHashMap;

use crate::{
    condition::Condition,
    definition::BackendDefinition,
    diagnostic,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::Predicate,
    rule::{
        ClassifiedAxiom, Concreteness, ConstraintKind, RewriteRule, applicable_groups, term_index,
    },
    simplify::{SimplificationOptions, simplify, simplify_predicate_with_solver},
    smt::NoSolver,
    substitution::{Substitution, substitute},
    term::{CollectionMetadata, HeadRole, Sort, SortNode, Term, TermKind, Variable},
};

use crate::confluence::{UnjoinedPair, symbols::Class};

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

/// A ground instance of an unjoined pair's overlap at which both equations apply and the two
/// reducts evaluate to two different normal forms, or to a normal form and an undefined value
/// (the parent module's "Findings: genuine or undecided").
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
    /// Which stuck applications each value holds, in the same order: `None` for a value built
    /// from data only, [`Stuck::Total`] for a defined value holding a stuck total application,
    /// [`Stuck::Partial`] for an undefined value. At most one side is [`Stuck::Partial`].
    pub stuck: (Option<Stuck>, Option<Stuck>),
}

/// What a value of a [`GroundInstance`] holds beyond data (the module documentation, "Stuck
/// applications").
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Stuck {
    /// A stuck application of a declared total function: the value is a normal form of `M_NF`
    /// that no equation names.
    Total,
    /// A stuck application of a declared partial function: the value is `\bottom` in `M_NF`,
    /// while the evaluator returns the stuck term.
    Partial,
}

/// How a term reads in `M_NF` (the module documentation, "Stuck applications").
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Reading {
    /// Built from data only.
    Data,
    /// Defined, holding a stuck total application.
    Total,
    /// Undefined: holding a stuck partial application.
    Undefined,
}

impl Reading {
    fn stuck(self) -> Option<Stuck> {
        match self {
            Self::Data => None,
            Self::Total => Some(Stuck::Total),
            Self::Undefined => Some(Stuck::Partial),
        }
    }
}

/// The search over one definition, with the candidates of each sort computed once.
pub(super) struct Search<'d> {
    definition: &'d BackendDefinition,
    candidates: FxHashMap<(Sort, usize), Vec<Term>>,
    /// The symbols that root a `non-executable` function equation or simplification lemma: the
    /// load keeps no rule of it to match, so an application of such a symbol is never read as
    /// stuck.
    unapplied: BTreeSet<String>,
}

impl<'d> Search<'d> {
    pub(super) fn new(definition: &'d BackendDefinition) -> Self {
        let unapplied = definition
            .classified_axioms()
            .iter()
            .filter(|axiom| !axiom.attributes().executable)
            .filter_map(|axiom| match axiom {
                ClassifiedAxiom::Function { lhs, .. }
                | ClassifiedAxiom::Simplification { lhs, .. } => match lhs {
                    KorePattern::Application { symbol, .. } => Some(symbol.name.clone()),
                    _ => None,
                },
                ClassifiedAxiom::Rewrite { .. } | ClassifiedAxiom::Ceil { .. } => None,
            })
            .collect();
        Self {
            definition,
            candidates: FxHashMap::default(),
            unapplied,
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
        if !well_formed_collections(&instance) {
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
        let ((left, left_reading), (right, right_reading)) = values?;
        let apart = match (left_reading, right_reading) {
            (Reading::Undefined, Reading::Undefined) => false,
            (Reading::Undefined, _) | (_, Reading::Undefined) => true,
            _ => left != right,
        };
        if !apart
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
            stuck: (left_reading.stuck(), right_reading.stuck()),
        })
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

    /// The value `term` evaluates to, with how it reads in `M_NF`, when it evaluates
    /// unconditionally, within the budget, to a ground term that is defined or undefined (the
    /// module documentation, "Stuck applications").
    fn value(&self, term: &Term) -> Option<(Term, Reading)> {
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
        if !value.attributes().variables.is_empty() {
            return None;
        }
        if self.definition.built_from_data(&value, &BTreeSet::new()) {
            return Some((value, Reading::Data));
        }
        let reading = self.reading(&value)?;
        Some((value, reading))
    }

    /// How the ground term `term` reads in `M_NF` (the module documentation, "Stuck
    /// applications"): `None` when it is neither defined nor undefined.
    fn reading(&self, term: &Term) -> Option<Reading> {
        if term.attributes().constructor_like {
            return Some(Reading::Data);
        }
        let distinct = |items: &[&Term]| items.windows(2).all(|pair| pair[0] != pair[1]);
        match term.kind() {
            TermKind::DomainValue { .. } => Some(Reading::Data),
            TermKind::Injection { term, .. } => self.reading(term),
            TermKind::Application {
                symbol, arguments, ..
            } => {
                let role = symbol.attributes.head_role();
                if role == HeadRole::FreeConstructor {
                    return self.readings(arguments);
                }
                let class = Class::of(symbol);
                let reading = if class.stuck_is_bottom() && !matches!(class, Class::Hooked { .. }) {
                    if crate::confluence::switches::active().stuck_partial_is_value {
                        Reading::Total
                    } else {
                        Reading::Undefined
                    }
                } else if matches!(class, Class::Total { .. })
                    && matches!(role, HeadRole::Function { declared: true, .. })
                    && symbol.attributes.hook.is_none()
                    && symbol.attributes.algebraic_axioms().is_empty()
                {
                    Reading::Total
                } else {
                    return None;
                };
                // Stuckness is read on defined arguments only: an equation tried on an undefined
                // argument says nothing in `M_NF`.
                if self.readings(arguments)? == Reading::Undefined || !self.stuck(term) {
                    return None;
                }
                Some(reading)
            }
            // Entries and elements are sorted, so an item held twice follows its first instance.
            TermKind::Map { entries, rest, .. } => {
                let keys = entries.iter().map(|(key, _)| key).collect::<Vec<_>>();
                if rest.is_some() || !distinct(&keys) {
                    return None;
                }
                self.readings(entries.iter().flat_map(|(key, value)| [key, value]))
            }
            TermKind::List { heads, rest, .. } => {
                if rest.is_some() {
                    return None;
                }
                self.readings(heads)
            }
            TermKind::Set { elements, rest, .. } => {
                if rest.is_some() || !distinct(&elements.iter().collect::<Vec<_>>()) {
                    return None;
                }
                self.readings(elements)
            }
            TermKind::Variable(_) | TermKind::And(..) => None,
        }
    }

    /// How a term built of `items` reads: undefined when one of them is, otherwise defined with
    /// a stuck total application when one of them holds one, otherwise data.
    fn readings<'t>(&self, items: impl IntoIterator<Item = &'t Term>) -> Option<Reading> {
        items.into_iter().try_fold(Reading::Data, |reading, item| {
            Some(reading.max(self.reading(item)?))
        })
    }

    /// Whether the ground application `application` is stuck: every equation the evaluator
    /// offers at it fails to match it or matches with its `requires` evaluating to `false`, and
    /// so does every axiom at its index the evaluator does not apply there (a `symbolic`
    /// equation, a `simplification` lemma), and no `non-executable` equation or lemma is rooted
    /// at its symbol (the load keeps none of them to match). Such an axiom that matched would
    /// equate the application with another term in every model, so its value would say nothing
    /// about the pair (the module documentation, "Stuck applications").
    fn stuck(&self, application: &Term) -> bool {
        if let TermKind::Application { symbol, .. } = application.kind()
            && self.unapplied.contains(symbol.name.as_ref())
        {
            return false;
        }
        let index = term_index(application);
        [
            self.definition.function_theory(),
            self.definition.simplification_theory(),
        ]
        .into_iter()
        .flat_map(|theory| applicable_groups(theory, &index).into_values().flatten())
        .all(|rule| self.matches(&rule, application) == Some(false))
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
                Some("STRING.String" | "BYTES.Bytes") => &["", "a"],
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

/// Whether every map and set in `term` is keyed by distinct normal forms: no key or element
/// occurs twice (on k-rust's internal normal form). Otherwise the collection is `\bottom`, no
/// normal form, and no equation applies at it.
fn well_formed_collections(term: &Term) -> bool {
    let distinct = |items: &[&Term]| {
        items
            .iter()
            .enumerate()
            .all(|(index, left)| !items[index + 1..].contains(left))
    };
    let collections_apart = match term.kind() {
        TermKind::Map { entries, .. } => {
            distinct(&entries.iter().map(|(key, _)| key).collect::<Vec<_>>())
        }
        TermKind::Set { elements, .. } => distinct(&elements.iter().collect::<Vec<_>>()),
        _ => true,
    };
    collections_apart && subterms(term).iter().all(well_formed_collections)
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

#[cfg(test)]
mod tests;
