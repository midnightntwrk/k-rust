//! V2 and V2b: the check's unifier and the matcher against the oracle's own reading of the
//! injection and overload axioms, over normal-form instances.
//!
//! The signature holds a subsort diamond (`C, D < A, B < T`), an overload family that stage 1
//! finds confluent (`consE`, `nilE` over `consN`, `nilN`), and one it does not (`g2` over `l1` and
//! `l2`, whose arguments' sorts share the subsort `Cc` with no lesser production below both). Its
//! only equations are the overload equations, so the oracle's normal form of a ground term is its
//! lowest form, and two ground terms are equal modulo the axioms exactly when their lowest forms
//! are the same.
//!
//! - **V2, soundness.** Every unifier, its free variables grounded by normal forms, makes the two
//!   terms equal modulo the axioms.
//! - **V2, completeness.** Every pair of valuations by normal forms that makes the two terms equal
//!   is an instance of a returned unifier, unless the unifier answered an unresolved shape (at
//!   most 15 % of pairs).
//! - **V2b.** A successful match instantiates the pattern to the subject modulo the axioms; a
//!   failed one leaves no valuation by normal forms that does; deferrals are counted.

use std::collections::{BTreeMap, HashMap};

use k_rust_kore::kore::parser::parse_pattern;

use super::{
    Rng,
    checks::{backend, candidates_of, oracle_term, values},
    completeness::pattern_of,
    engine::{Id, Node, Universe},
    language::{Definition, Kind, Pat, app, cons, inj, int, pattern_kore, pattern_variables, var},
};
use crate::{
    confluence::{SettledRoot, unify_for_tests},
    definition::BackendDefinition,
    matching::{MatchResult, match_with_settled_evidence},
    substitution::substitute,
    term::{Term, head::NormalEvidence},
};

/// Valuations enumerated per term.
const VALUATIONS: usize = 200;

pub(super) fn signature() -> Definition {
    let total_head = Kind::Head {
        value_production: false,
        total: true,
    };
    let mut definition = Definition::new(&[
        "T", "A", "B", "C", "D", "E", "N", "Es", "Ns", "Hh", "Aa", "Bb", "Cc", "Tt",
    ])
    .subsort("C", "A")
    .subsort("C", "B")
    .subsort("D", "A")
    .subsort("D", "B")
    .subsort("A", "T")
    .subsort("B", "T")
    .constructor("a0", &[], "A")
    .constructor("b0", &[], "B")
    .constructor("c0", &[], "C")
    .constructor("d0", &[], "D")
    .constructor("pa", &["A"], "T")
    .constructor("pt", &["T", "T"], "T")
    .head("w", &["T"], "T")
    .subsort("N", "E")
    .subsort("Ns", "Es")
    .constructor("n0", &[], "N")
    .constructor("n1", &[], "N")
    .constructor("e0", &[], "E")
    .constructor("nilN", &[], "Ns")
    .constructor("consN", &["N", "Ns"], "Ns")
    .symbol("nilE", &[], "Es", total_head)
    .symbol("consE", &["E", "Es"], "Es", total_head)
    .overload("consE", "consN")
    .overload("nilE", "nilN")
    .subsort("Cc", "Aa")
    .subsort("Cc", "Bb")
    .subsort("Aa", "Tt")
    .subsort("Bb", "Tt")
    .constructor("c1", &[], "Cc")
    .constructor("l1", &["Aa"], "Hh")
    .constructor("l2", &["Bb"], "Hh")
    .symbol("g2", &["Tt"], "Hh", total_head)
    .overload("g2", "l1")
    .overload("g2", "l2");
    definition.sorts.retain(|sort| sort != "S");
    definition.sorts.insert(0, "S".into());
    definition
}

/// Random patterns over [`signature`].
struct Terms<'r> {
    rng: &'r mut Rng,
    definition: Definition,
    /// The variables' name suffix, so that the two sides of a pair are apart.
    suffix: &'static str,
}

impl Terms<'_> {
    fn term(&mut self, sort: &str, depth: usize) -> Pat {
        if sort == "Int" {
            return if self.rng.percent(50) {
                var(&format!("VarI{}", self.suffix), "Int")
            } else {
                int(i64::try_from(self.rng.below(2)).unwrap())
            };
        }
        if depth == 0 || self.rng.percent(30) {
            let index = self.rng.below(2);
            return var(&format!("Var{sort}{index}{}", self.suffix), sort);
        }
        let symbols = self
            .definition
            .symbols
            .iter()
            .filter(|symbol| symbol.result == sort && symbol.kind != Kind::Hook)
            .cloned()
            .collect::<Vec<_>>();
        let subsorts = self
            .definition
            .subsorts
            .iter()
            .filter(|(_, sup)| sup == sort)
            .map(|(sub, _)| sub.clone())
            .collect::<Vec<_>>();
        if !subsorts.is_empty() && (symbols.is_empty() || self.rng.percent(35)) {
            let sub = self.rng.pick(&subsorts).clone();
            let inner = self.term(&sub, depth - 1);
            if !matches!(inner, Pat::Inj(..)) {
                return inj(&sub, sort, inner);
            }
        }
        if symbols.is_empty() {
            return var(&format!("Var{sort}0{}", self.suffix), sort);
        }
        let symbol = self.rng.pick(&symbols).clone();
        if symbol.arguments.is_empty() {
            return cons(&symbol.name);
        }
        let arguments = symbol
            .arguments
            .iter()
            .map(|argument| self.term(argument, depth - 1))
            .collect();
        app(&symbol.name, arguments)
    }
}

/// The sorts pairs are drawn at.
const SORTS: [&str; 6] = ["T", "A", "B", "Es", "Hh", "Tt"];

fn internalize(backend: &BackendDefinition, pattern: &Pat) -> Term {
    backend
        .internalize_term(
            &parse_pattern(&pattern_kore(pattern)).expect("the pattern parses"),
            &[],
        )
        .expect("the pattern internalizes")
}

/// Valuations of `variables` by normal forms: all of them when few, else a sample.
fn valuations(
    universe: &mut Universe<'_>,
    values: &BTreeMap<u32, Vec<Id>>,
    variables: &BTreeMap<String, String>,
    rng: &mut Rng,
) -> Vec<HashMap<String, Id>> {
    let mut choices = Vec::new();
    for (name, sort) in variables {
        let Some(sort) = sort_id(universe, sort) else {
            return Vec::new();
        };
        let candidates = candidates_of(universe, values, sort);
        if candidates.is_empty() {
            return Vec::new();
        }
        choices.push((name.clone(), candidates));
    }
    let total = choices
        .iter()
        .try_fold(1usize, |product, (_, candidates)| {
            product.checked_mul(candidates.len())
        })
        .unwrap_or(usize::MAX);
    if total <= VALUATIONS {
        let mut all = vec![HashMap::new()];
        for (name, candidates) in &choices {
            let mut next = Vec::new();
            for valuation in &all {
                for candidate in candidates {
                    let mut extended: HashMap<String, Id> = valuation.clone();
                    extended.insert(name.clone(), *candidate);
                    next.push(extended);
                }
            }
            all = next;
        }
        all
    } else {
        (0..VALUATIONS)
            .map(|_| {
                choices
                    .iter()
                    .map(|(name, candidates)| (name.clone(), *rng.pick(candidates)))
                    .collect()
            })
            .collect()
    }
}

fn sort_id(universe: &Universe<'_>, sort: &str) -> Option<u32> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| universe.sort_id(sort))).ok()
}

/// Equality modulo the axioms on the explored terms: the equivalence closure of "a term equals
/// each of its lowest forms" (the overload equations are the signature's only equations). In a
/// confluent family each class has one lowest form; in a family that is not, two lowest forms of
/// one term, such as `l1(inj(c1))` and `l2(inj(c1))` from `g2(inj(c1))`, are one class.
///
/// A class with two lowest forms makes two distinct normal forms equal: the definition has no
/// model in which its constructors are free (`l1` and `l2` are), so nothing about its normal-form
/// instances can be wrong, and such classes are skipped ([`Classes::consistent`]).
#[derive(Default)]
struct Classes {
    parent: HashMap<Id, Id>,
    /// The lowest forms of each class, at its root.
    forms: HashMap<Id, std::collections::BTreeSet<Id>>,
}

impl Classes {
    /// Whether the class of `id` has at most one lowest form.
    fn consistent(&mut self, id: Id) -> bool {
        let root = self.find(id);
        self.forms.get(&root).is_none_or(|forms| forms.len() <= 1)
    }

    fn add_form(&mut self, id: Id, form: Id) {
        self.union(id, form);
        let root = self.find(id);
        self.forms.entry(root).or_default().insert(form);
    }

    fn find(&mut self, id: Id) -> Id {
        let parent = *self.parent.entry(id).or_insert(id);
        if parent == id {
            return id;
        }
        let root = self.find(parent);
        self.parent.insert(id, root);
        root
    }

    fn union(&mut self, left: Id, right: Id) {
        let (left, right) = (self.find(left), self.find(right));
        if left != right {
            self.parent.insert(left, right);
            if let Some(forms) = self.forms.remove(&left) {
                self.forms.entry(right).or_default().extend(forms);
            }
        }
    }

    /// Records the instance of `pattern` under `valuation` with its lowest forms; `None` when
    /// its lowering does not end.
    fn instance(
        &mut self,
        universe: &mut Universe<'_>,
        pattern: &Pat,
        valuation: &HashMap<String, Id>,
    ) -> Option<Id> {
        let instance = universe.instantiate(pattern, valuation);
        let normal = universe.normalize(instance);
        if !normal.complete || normal.forms.contains(&super::engine::BOTTOM) {
            return None;
        }
        for form in &normal.forms {
            self.add_form(instance, *form);
        }
        Some(instance)
    }

    /// Records every value, and every application of a greater overloaded production to values
    /// (the terms that lower), so that the classes hold what the overload axioms identify.
    fn observe_values(&mut self, universe: &mut Universe<'_>, values: &BTreeMap<u32, Vec<Id>>) {
        for ids in values.values() {
            for id in ids {
                let normal = universe.normalize(*id);
                for form in &normal.forms {
                    self.add_form(*id, *form);
                }
            }
        }
        let definition = universe.definition;
        let greater = definition
            .overloads()
            .into_iter()
            .map(|(greater, _)| greater)
            .collect::<std::collections::BTreeSet<_>>();
        for name in greater {
            let symbol = definition.symbol_named(&name).clone();
            let mut combinations = vec![Vec::new()];
            for sort in &symbol.arguments {
                let sort = universe.sort_id(sort);
                let candidates = candidates_of(universe, values, sort);
                let mut next = Vec::new();
                for combination in &combinations {
                    for candidate in candidates.iter().take(6) {
                        let mut extended: Vec<Id> = combination.clone();
                        extended.push(*candidate);
                        next.push(extended);
                    }
                }
                combinations = next;
            }
            let symbol_id = universe.symbol_id(&name);
            for arguments in combinations {
                let application = universe.node(super::engine::Node::App(symbol_id, arguments));
                let normal = universe.normalize(application);
                for form in &normal.forms {
                    self.add_form(application, *form);
                }
            }
        }
    }
}

#[derive(Debug, Default)]
pub(super) struct UnifierTally {
    pub(super) pairs: usize,
    pub(super) unified: usize,
    pub(super) unresolved: usize,
    pub(super) equal_instances: usize,
    pub(super) matches: usize,
    pub(super) deferred: usize,
    /// Deferrals on an equation-head application of the pattern (documented partial).
    pub(super) deferred_heads: usize,
    /// A sample of the deferrals.
    pub(super) deferrals: Vec<String>,
    pub(super) failures: Vec<String>,
}

/// V2 on `cases` random pairs.
pub(super) fn run_unifier(cases: u64, seed: u64) -> UnifierTally {
    let definition = signature();
    let backend = backend(&definition).expect("the signature internalizes");
    let mut tally = UnifierTally::default();
    let mut universe = Universe::new(&definition);
    let mut rng = Rng(seed ^ 0x0002);
    let values = values(&mut universe, &mut rng);
    let mut classes = Classes::default();
    classes.observe_values(&mut universe, &values);
    for case in 0..cases {
        let sort = *rng.pick(&SORTS);
        let mut terms = Terms {
            rng: &mut rng,
            definition: definition.clone(),
            suffix: "",
        };
        let left = terms.term(sort, 3);
        terms.suffix = "R";
        let right = terms.term(sort, 3);
        tally.pairs += 1;
        let (left_term, right_term) = (internalize(&backend, &left), internalize(&backend, &right));
        let unifiers = match unify_for_tests(&backend, &left_term, &right_term) {
            Ok(unifiers) => unifiers,
            Err(_) => {
                tally.unresolved += 1;
                continue;
            }
        };
        tally.unified += 1;
        let shown = format!(
            "case {case}: {} = {}",
            super::checks::show(&left),
            super::checks::show(&right)
        );
        // Soundness.
        for unifier in &unifiers {
            let (left_instance, right_instance) = (
                substitute(&left_term, unifier),
                substitute(&right_term, unifier),
            );
            let (Some(left_pattern), Some(right_pattern)) =
                (pattern_of(&left_instance), pattern_of(&right_instance))
            else {
                continue;
            };
            let mut free = BTreeMap::new();
            pattern_variables(&left_pattern, &mut free);
            pattern_variables(&right_pattern, &mut free);
            let groundings = valuations(&mut universe, &values, &free, &mut rng);
            for grounding in groundings.iter().take(8) {
                let left_value = classes.instance(&mut universe, &left_pattern, grounding);
                let right_value = classes.instance(&mut universe, &right_pattern, grounding);
                let (Some(left_value), Some(right_value)) = (left_value, right_value) else {
                    continue;
                };
                if !classes.consistent(left_value) || !classes.consistent(right_value) {
                    continue;
                }
                if classes.find(left_value) != classes.find(right_value) {
                    tally.failures.push(format!(
                        "{shown}: the unifier {unifier:?} grounds to {} and {}",
                        universe.show(left_value),
                        universe.show(right_value),
                    ));
                    break;
                }
            }
        }
        // Completeness.
        let mut left_variables = BTreeMap::new();
        pattern_variables(&left, &mut left_variables);
        let mut left_instances = Vec::new();
        for valuation in valuations(&mut universe, &values, &left_variables, &mut rng) {
            if let Some(value) = classes.instance(&mut universe, &left, &valuation) {
                left_instances.push((value, valuation));
            }
        }
        let mut right_variables = BTreeMap::new();
        pattern_variables(&right, &mut right_variables);
        let mut right_instances = Vec::new();
        for valuation in valuations(&mut universe, &values, &right_variables, &mut rng) {
            if let Some(value) = classes.instance(&mut universe, &right, &valuation) {
                right_instances.push((value, valuation));
            }
        }
        let mut by_value = HashMap::<Id, Vec<HashMap<String, Id>>>::new();
        for (value, valuation) in left_instances {
            by_value
                .entry(classes.find(value))
                .or_default()
                .push(valuation);
        }
        'valuations: for (value, valuation) in right_instances {
            if !classes.consistent(value) {
                continue;
            }
            let value = classes.find(value);
            for left_valuation in by_value.get(&value).into_iter().flatten() {
                tally.equal_instances += 1;
                let mut joint = left_valuation.clone();
                joint.extend(valuation.clone());
                if !covered(
                    &mut universe,
                    &unifiers,
                    &left_variables,
                    &right_variables,
                    &joint,
                ) {
                    tally.failures.push(format!(
                        "{shown}: the instances at {:?} are both {} and no unifier generalizes them (unifiers {unifiers:?})",
                        joint
                            .iter()
                            .map(|(name, id)| format!("{name} = {}", universe.show(*id)))
                            .collect::<Vec<_>>(),
                        universe.show(value)
                    ));
                    break 'valuations;
                }
            }
        }
        if tally.failures.len() >= 20 {
            break;
        }
    }
    tally
}

fn covered(
    universe: &mut Universe<'_>,
    unifiers: &[crate::substitution::Substitution],
    left: &BTreeMap<String, String>,
    right: &BTreeMap<String, String>,
    valuation: &HashMap<String, Id>,
) -> bool {
    unifiers.iter().any(|unifier| {
        let mut shared = HashMap::new();
        left.iter().chain(right).all(|(name, _)| {
            let bound = unifier
                .iter()
                .find(|(variable, _)| variable.name.as_ref() == name)
                .map(|(_, value)| value.clone());
            let pattern = match bound {
                Some(value) => match pattern_of(&value) {
                    Some(pattern) => pattern,
                    None => return true,
                },
                None => {
                    let sort = &left.get(name).or_else(|| right.get(name)).unwrap();
                    var(name, sort)
                }
            };
            universe.matches(&pattern, valuation[name], &mut shared)
        })
    })
}

/// V2b on `cases` random pattern-subject pairs.
pub(super) fn run_matcher(cases: u64, seed: u64) -> UnifierTally {
    let definition = signature();
    let backend = backend(&definition).expect("the signature internalizes");
    let mut tally = UnifierTally::default();
    let mut universe = Universe::new(&definition);
    let mut rng = Rng(seed ^ 0x0003);
    let values = values(&mut universe, &mut rng);
    let mut classes = Classes::default();
    classes.observe_values(&mut universe, &values);
    let evidence = |_: &Term| Some(NormalEvidence::settled(SettledRoot::for_tests()));
    for case in 0..cases {
        let sort = *rng.pick(&SORTS);
        let pattern = Terms {
            rng: &mut rng,
            definition: definition.clone(),
            suffix: "",
        }
        .term(sort, 3);
        let sort_index = universe.sort_id(sort);
        let subjects = candidates_of(&mut universe, &values, sort_index);
        if subjects.is_empty() {
            continue;
        }
        let subject = *rng.pick(&subjects);
        if !classes.consistent(subject) {
            continue;
        }
        // The evaluator tries an equation only on a subject at the equation's index: a pattern
        // rooted at an equation head is matched against applications of that head.
        if let (Pat::App(name, _), Node::App(symbol, _)) = (&pattern, universe.node_of(subject))
            && definition.symbol_named(name).is_head()
            && definition.symbols[*symbol as usize].name != *name
        {
            continue;
        }
        if matches!(&pattern, Pat::App(name, _) if definition.symbol_named(name).is_head())
            && !matches!(universe.node_of(subject), Node::App(..))
        {
            continue;
        }
        let subject_term = backend
            .internalize_term(
                &parse_pattern(&universe.kore(subject)).expect("the subject parses"),
                &[],
            )
            .expect("the subject internalizes");
        let pattern_term = internalize(&backend, &pattern);
        tally.matches += 1;
        let shown = format!(
            "case {case}: {} against {}",
            super::checks::show(&pattern),
            universe.show(subject)
        );
        match match_with_settled_evidence(&backend, &pattern_term, &subject_term, &evidence) {
            MatchResult::Success(substitution) => {
                let mut valuation = HashMap::new();
                let mut known = true;
                for (variable, value) in &substitution {
                    match oracle_term(&mut universe, value) {
                        Some(id) => {
                            valuation.insert(variable.name.to_string(), id);
                        }
                        None => known = false,
                    }
                }
                let mut variables = BTreeMap::new();
                pattern_variables(&pattern, &mut variables);
                if !known || variables.keys().any(|name| !valuation.contains_key(name)) {
                    continue;
                }
                let instance = classes.instance(&mut universe, &pattern, &valuation);
                if instance.is_none_or(|instance| classes.find(instance) != classes.find(subject)) {
                    tally.failures.push(format!(
                        "{shown}: the match {substitution:?} does not instantiate the pattern to the subject"
                    ));
                }
            }
            MatchResult::Failed(reason) => {
                let mut variables = BTreeMap::new();
                pattern_variables(&pattern, &mut variables);
                for valuation in valuations(&mut universe, &values, &variables, &mut rng) {
                    let instance = classes.instance(&mut universe, &pattern, &valuation);
                    if instance
                        .is_some_and(|instance| classes.find(instance) == classes.find(subject))
                    {
                        tally.failures.push(format!(
                            "{shown}: the match failed ({reason:?}) but {:?} instantiates the pattern to the subject",
                            valuation
                                .iter()
                                .map(|(name, id)| format!("{name} = {}", universe.show(*id)))
                                .collect::<Vec<_>>()
                        ));
                        break;
                    }
                }
            }
            MatchResult::Indeterminate { remainder, .. }
                if remainder.iter().any(|(pattern, _)| {
                    matches!(pattern.kind(), crate::term::TermKind::Application { symbol, .. }
                        if symbol.attributes.head_role() == crate::term::HeadRole::EquationHead)
                }) =>
            {
                // The documented partial shape: an equation-head application in the pattern
                // against a subject term of another root, which the instance of the pattern may
                // equal through the head's equations (`RootPolicy::Undecided`).
                tally.deferred_heads += 1;
            }
            MatchResult::Indeterminate { remainder, .. } => {
                tally.deferred += 1;
                if tally.deferrals.len() < 8 {
                    tally.deferrals.push(format!(
                        "{shown}: deferred on {}",
                        remainder
                            .iter()
                            .map(|(pattern, subject)| format!("{pattern:?} against {subject:?}"))
                            .collect::<Vec<_>>()
                            .join("; ")
                    ));
                }
            }
        }
        if tally.failures.len() >= 20 {
            break;
        }
    }
    tally
}

#[test]
fn the_unifier_is_sound_and_complete_over_normal_form_instances() {
    super::on_large_stack(|| {
        let cases = super::environment("KRUST_DEFINEDNESS_ORACLE_CASES", super::DEFAULT_CASES);
        let seed = super::environment("KRUST_DEFINEDNESS_ORACLE_SEED", super::DEFAULT_SEED);
        let tally = run_unifier(cases * 80, seed);
        eprintln!(
            "unifier (seed {seed:#x}): {} pairs, {} unified, {} unresolved, {} pairs of equal instances, {} failures",
            tally.pairs,
            tally.unified,
            tally.unresolved,
            tally.equal_instances,
            tally.failures.len()
        );
        let mut failures = tally.failures;
        if tally.unresolved * 100 > tally.pairs * 15 {
            failures.push(format!(
                "{} of {} pairs unresolved (ceiling 15 %)",
                tally.unresolved, tally.pairs
            ));
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    });
}

#[test]
fn the_matcher_agrees_with_the_axioms_on_normal_form_subjects() {
    super::on_large_stack(|| {
        let cases = super::environment("KRUST_DEFINEDNESS_ORACLE_CASES", super::DEFAULT_CASES);
        let seed = super::environment("KRUST_DEFINEDNESS_ORACLE_SEED", super::DEFAULT_SEED);
        let tally = run_matcher(cases * 200, seed);
        eprintln!(
            "matcher (seed {seed:#x}): {} matches, {} deferred on an equation-head application of the pattern, {} other deferrals, {} failures",
            tally.matches,
            tally.deferred_heads,
            tally.deferred,
            tally.failures.len()
        );
        for deferral in &tally.deferrals {
            eprintln!("  {deferral}");
        }
        let mut failures = tally.failures;
        if tally.deferred > 0 {
            failures.push(format!(
                "{} deferrals on ground lowest-form subjects (ceiling 0): {}",
                tally.deferred,
                tally.deferrals.join("\n")
            ));
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    });
}
