//! The checks of one definition against the oracle's normal-form model: V4 (unique normal forms
//! on accepted definitions), V5 (every claim agrees with `M_NF` there), and V6 (on definitions
//! with non-joined pairs: (a) the taint set recomputed by the oracle, (c) no claim on a tainted
//! term, and (b) the claims on untainted terms whose evaluation applies only untainted equations
//! agree with their unique normal form), and V6 (d) on every definition with a model: no claim on
//! a term, or a generalization of one, that every model makes undefined (`forced.rs`).

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::Write as _,
    panic::{AssertUnwindSafe, catch_unwind},
};

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::{
    Rng,
    engine::{BOTTOM, Id, Node, Universe},
    language::{Definition, Kind, Pat, equation_index, pattern_variables},
};
use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    simplify::{SimplificationOptions, simplify, simplify_predicate_with_solver},
    smt::NoSolver,
    term::{Sort, Term, TermKind, head::certified_ground_normal_form},
};

/// Queries per definition, values per sort, and instances per generalization.
const QUERIES: usize = 40;

/// Instances of each left-hand side among the roots of the V6 (d) derivation.
const FORCED_INSTANCES: usize = 8;

/// The mark of a V6 (d) failure, which the mutation tests of review 1's classes look for.
pub(super) const FORCED: &str = "V6 (d)";

/// The tag of V9's failures: the load's scope and the full check differ on a claim or a warning.
pub(super) const SCOPES: &str = "V9";

/// The tag of the memo's failures: the full check with and without its memo of condition
/// simplifications differ in a verdict or a count other than the memo's hits.
pub(super) const MEMO: &str = "memo";

/// Where the counts of `on`, a verdict computed with the memo of condition simplifications, and
/// `off`, the same check's without it, differ beyond the memo's own hits, if anywhere.
pub(super) fn memo_count_difference(
    on: &crate::confluence::ValueClaims,
    off: &crate::confluence::ValueClaims,
) -> Option<String> {
    let mut expected = on.counts();
    expected.condition_memo_hits = 0;
    (expected != off.counts()).then(|| {
        format!(
            "counts with the memo {:?} against without {:?}",
            on.counts(),
            off.counts()
        )
    })
}

const VALUES_PER_SORT: usize = 8;
const VALUATIONS_PER_EQUATION: usize = 4;

/// Feature classes of the generated definitions, counted against the floors.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum Class {
    Conditional,
    Ensures,
    Collection,
    Priority,
    Overload,
    Diamond,
    NonConfluentFamily,
    Chain,
    Observation,
    Erasing,
    IrrelevantCluster,
    NoHead,
}

impl Class {
    pub(super) const ALL: [Self; 12] = [
        Self::Conditional,
        Self::Ensures,
        Self::Collection,
        Self::Priority,
        Self::Overload,
        Self::Diamond,
        Self::NonConfluentFamily,
        Self::Chain,
        Self::Observation,
        Self::Erasing,
        Self::IrrelevantCluster,
        Self::NoHead,
    ];
}

/// What the checks of one or more definitions counted and found.
#[derive(Debug, Default)]
pub(super) struct Tally {
    pub(super) definitions: usize,
    /// Rejected by parsing or internalization (ceiling 0).
    pub(super) rejected: usize,
    /// With no non-joined pair and no precondition violation.
    pub(super) accepted: usize,
    /// With some equation head tainted and some not.
    pub(super) partially_tainted: usize,
    /// Outside P2: a total symbol undefined on defined arguments was reached.
    pub(super) outside_totality: usize,
    pub(super) queries: usize,
    /// Queries whose evaluation did not end within the bounds (outside P0).
    pub(super) nonterminating: usize,
    pub(super) tokens: usize,
    pub(super) certificates: usize,
    pub(super) apartness: usize,
    pub(super) ceilings: usize,
    pub(super) generalizations: usize,
    /// Claims withheld on tainted terms (property A).
    pub(super) withheld: usize,
    /// Marker claims (an irreducible value-production application is defined) checked.
    pub(super) markers: usize,
    /// Queries whose evaluation by the backend ends in a certified value other than their
    /// normal form under `->E`, and a sample of them.
    pub(super) divergent: usize,
    pub(super) divergences: Vec<String>,
    /// V6 (d): queries every model of a definition with a model makes undefined, and
    /// definitions shown to have no model (where nothing is checked).
    pub(super) forced_undefined: usize,
    pub(super) without_model: usize,
    pub(super) classes: BTreeMap<Class, usize>,
    /// The reasons of the non-joined pairs, counted.
    pub(super) reasons: BTreeMap<String, usize>,
    /// The conditions the full check simplified, and those of them the memo answered.
    pub(super) memo_conditions: usize,
    pub(super) memo_hits: usize,
    /// Definitions whose load skipped a pair the full check classifies (`CheckCounts::skipped`):
    /// those on which V9 compares the two scopes where they could differ.
    pub(super) with_skipped_pair: usize,
    pub(super) failures: Vec<String>,
}

impl Tally {
    pub(super) fn add(&mut self, other: Self) {
        self.definitions += other.definitions;
        self.rejected += other.rejected;
        self.accepted += other.accepted;
        self.partially_tainted += other.partially_tainted;
        self.outside_totality += other.outside_totality;
        self.queries += other.queries;
        self.nonterminating += other.nonterminating;
        self.tokens += other.tokens;
        self.certificates += other.certificates;
        self.apartness += other.apartness;
        self.ceilings += other.ceilings;
        self.generalizations += other.generalizations;
        self.withheld += other.withheld;
        self.markers += other.markers;
        self.divergent += other.divergent;
        self.forced_undefined += other.forced_undefined;
        self.without_model += other.without_model;
        self.memo_conditions += other.memo_conditions;
        self.memo_hits += other.memo_hits;
        self.with_skipped_pair += other.with_skipped_pair;
        if self.divergences.len() < 5 {
            self.divergences.extend(other.divergences);
            self.divergences.truncate(5);
        }
        for (class, count) in other.classes {
            *self.classes.entry(class).or_default() += count;
        }
        for (reason, count) in other.reasons {
            *self.reasons.entry(reason).or_default() += count;
        }
        self.failures.extend(other.failures);
    }

    pub(super) fn summary(&self, name: &str) -> String {
        format!(
            "{name}: {} definitions ({} rejected, {} accepted, {} partially tainted, {} outside P2), {} queries ({} outside P0), positive claims checked: {} tokens, {} certificates, {} marker claims, {} apartness, {} \\ceil discharges, {} generalizations; {} claims withheld on tainted terms; {} evaluations diverging from ->E; {} queries undefined in every model, {} definitions without a model; classes {:?}; {} failures",
            self.definitions,
            self.rejected,
            self.accepted,
            self.partially_tainted,
            self.outside_totality,
            self.queries,
            self.nonterminating,
            self.tokens,
            self.certificates,
            self.markers,
            self.apartness,
            self.ceilings,
            self.generalizations,
            self.withheld,
            self.divergent,
            self.forced_undefined,
            self.without_model,
            self.classes,
            self.failures.len()
        ) + &format!(
            "; non-joined pairs by reason {:?}; {} of the full check's {} conditions answered from the memo; {} definitions with a pair the load's scope skipped",
            self.reasons, self.memo_hits, self.memo_conditions, self.with_skipped_pair
        )
    }
}

/// What the check of one definition found besides its tally.
#[derive(Debug, Default)]
pub(super) struct Verdict {
    /// The backend reported no non-joined pair and no violation.
    pub(super) accepted: bool,
    /// The tainted symbols, as the backend computed them.
    pub(super) tainted: BTreeSet<String>,
    /// For each probe query: (whether its `\ceil` obligation was kept, whether it got a token).
    pub(super) probes: Vec<(bool, bool)>,
}

/// The parsed and internalized backend definition, or why there is none.
pub(super) fn backend(definition: &Definition) -> Result<BackendDefinition, String> {
    let source = definition.kore();
    let syntax = parse_definition(&source).map_err(|error| format!("parse: {error:?}"))?;
    catch_unwind(AssertUnwindSafe(|| {
        BackendDefinition::internalize(&syntax, "MAIN")
    }))
    .map_err(|_| "internalization panicked".to_owned())?
    .map_err(|error| format!("internalize: {error:?}"))
}

/// The feature classes `definition` exhibits, read syntactically.
pub(super) fn classes(definition: &Definition) -> BTreeSet<Class> {
    let mut classes = BTreeSet::new();
    let heads = definition
        .symbols
        .iter()
        .filter(|symbol| symbol.is_head())
        .map(|symbol| symbol.name.as_str())
        .collect::<HashSet<_>>();
    if heads.is_empty() {
        classes.insert(Class::NoHead);
    }
    for equation in &definition.equations {
        if equation.requires.is_some() {
            classes.insert(Class::Conditional);
        }
        if equation.ensures.is_some() {
            classes.insert(Class::Ensures);
        }
        if equation.priority != super::language::DEFAULT_PRIORITY {
            classes.insert(Class::Priority);
        }
        if has_list(&equation.lhs) {
            classes.insert(Class::Collection);
        }
        if let Pat::App(_, arguments) = &equation.lhs
            && arguments.iter().any(|argument| mentions(argument, &heads))
        {
            classes.insert(Class::Chain);
        }
        // An erasing equation: a left-hand side variable its right-hand side drops.
        let (mut left, mut right) = (BTreeMap::new(), BTreeMap::new());
        pattern_variables(&equation.lhs, &mut left);
        pattern_variables(&equation.rhs, &mut right);
        if equation.overload.is_none() && left.keys().any(|name| !right.contains_key(name)) {
            classes.insert(Class::Erasing);
        }
    }
    let overloads = definition.overloads();
    if !overloads.is_empty() {
        classes.insert(Class::Overload);
    }
    // A diamond: a lesser production with two incomparable greater ones.
    for (greater, lesser) in &overloads {
        if overloads.iter().any(|(other, below)| {
            below == lesser
                && other != greater
                && !overloads.contains(&(greater.clone(), other.clone()))
                && !overloads.contains(&(other.clone(), greater.clone()))
        }) {
            classes.insert(Class::Diamond);
        }
    }
    // A family whose greater production lowers to two incomparable lesser ones with no common
    // lesser production.
    for (greater, lesser) in &overloads {
        if overloads.iter().any(|(other, below)| {
            other == greater
                && below != lesser
                && !overloads.contains(&(lesser.clone(), below.clone()))
                && !overloads.contains(&(below.clone(), lesser.clone()))
                && !overloads.iter().any(|(middle, least)| {
                    middle == lesser && overloads.contains(&(below.clone(), least.clone()))
                })
        }) {
            classes.insert(Class::NonConfluentFamily);
        }
    }
    // A variable of a sort some equation head's applications inhabit.
    let head_sorts = definition
        .symbols
        .iter()
        .filter(|symbol| symbol.is_head())
        .map(|symbol| symbol.result.clone())
        .collect::<HashSet<_>>();
    if definition.equations.iter().any(|equation| {
        let mut variables = BTreeMap::new();
        pattern_variables(&equation.lhs, &mut variables);
        variables.values().any(|sort| head_sorts.contains(sort))
    }) {
        classes.insert(Class::Observation);
    }
    // A cluster: functions over a sort no head's applications reach.
    if definition.sorts.iter().any(|sort| sort.starts_with('Z')) {
        classes.insert(Class::IrrelevantCluster);
    }
    classes
}

fn has_list(pattern: &Pat) -> bool {
    match pattern {
        Pat::List(..) => true,
        Pat::App(_, arguments) => arguments.iter().any(has_list),
        Pat::Inj(_, _, inner) | Pat::As(inner, _, _) => has_list(inner),
        Pat::Var(..) | Pat::Int(_) => false,
    }
}

fn mentions(pattern: &Pat, names: &HashSet<&str>) -> bool {
    match pattern {
        Pat::App(name, arguments) => {
            names.contains(name.as_str())
                || arguments.iter().any(|argument| mentions(argument, names))
        }
        Pat::Inj(_, _, inner) | Pat::As(inner, _, _) => mentions(inner, names),
        Pat::List(prefix, _, suffix) => prefix
            .iter()
            .chain(suffix)
            .any(|element| mentions(element, names)),
        Pat::Var(..) | Pat::Int(_) => false,
    }
}

/// The values the oracle explores, by sort: ground normal forms other than `\bottom`, built
/// bottom-up from literals, constructors, equation heads and functions, and injections.
pub(super) fn values(universe: &mut Universe<'_>, rng: &mut Rng) -> BTreeMap<u32, Vec<Id>> {
    let definition = universe.definition;
    let mut values = BTreeMap::<u32, Vec<Id>>::new();
    let add = |universe: &mut Universe<'_>, values: &mut BTreeMap<u32, Vec<Id>>, id: Id| {
        let sort = universe.sort_of(id);
        let entry = values.entry(sort).or_default();
        if !entry.contains(&id) && entry.len() < VALUES_PER_SORT {
            entry.push(id);
        }
    };
    let mut literals = literals(definition);
    literals.truncate(5);
    for literal in &literals {
        let id = universe.int(*literal);
        add(universe, &mut values, id);
    }
    for truth in [true, false] {
        let id = universe.boolean(truth);
        add(universe, &mut values, id);
    }
    if definition.lists {
        let empty = universe.node(Node::List(Vec::new()));
        add(universe, &mut values, empty);
        for literal in literals.iter().take(2) {
            let element = universe.int(*literal);
            let single = universe.node(Node::List(vec![element]));
            add(universe, &mut values, single);
            let other = universe.int(literals[0]);
            let pair = universe.node(Node::List(vec![other, element]));
            add(universe, &mut values, pair);
        }
    }
    for _round in 0..3 {
        for symbol in &definition.symbols {
            if symbol.kind == Kind::Hook {
                continue;
            }
            let symbol_id = universe.symbol_id(&symbol.name);
            for _ in 0..3 {
                let mut arguments = Vec::new();
                for sort in &symbol.arguments {
                    let sort = universe.sort_id(sort);
                    let candidates = candidates_of(universe, &values, sort);
                    if candidates.is_empty() {
                        break;
                    }
                    arguments.push(*rng.pick(&candidates));
                }
                if arguments.len() != symbol.arguments.len() {
                    break;
                }
                let application = universe.node(Node::App(symbol_id, arguments));
                if universe.size(application) > 9 {
                    continue;
                }
                let normal = universe.normalize(application);
                if !normal.complete {
                    continue;
                }
                for form in normal.forms.clone() {
                    if form != BOTTOM && universe.size(form) <= 9 {
                        add(universe, &mut values, form);
                    }
                }
            }
        }
    }
    values
}

/// The values of `sort` and the injections of the values of its subsorts.
pub(super) fn candidates_of(
    universe: &mut Universe<'_>,
    values: &BTreeMap<u32, Vec<Id>>,
    sort: u32,
) -> Vec<Id> {
    let mut candidates = Vec::new();
    for (value_sort, ids) in values {
        if universe.is_subsort(*value_sort, sort) {
            for id in ids {
                let injected = universe.node(Node::Inj(*value_sort, sort, *id));
                candidates.push(injected);
            }
        }
    }
    candidates
}

/// The Int literals the definition mentions, and 0 to 3.
pub(super) fn literals(definition: &Definition) -> Vec<i64> {
    fn collect(pattern: &Pat, into: &mut BTreeSet<i64>) {
        match pattern {
            Pat::Int(value) => {
                into.insert(*value);
            }
            Pat::App(_, arguments) => {
                for argument in arguments {
                    collect(argument, into);
                }
            }
            Pat::Inj(_, _, inner) | Pat::As(inner, _, _) => collect(inner, into),
            Pat::List(prefix, _, suffix) => {
                for element in prefix.iter().chain(suffix) {
                    collect(element, into);
                }
            }
            Pat::Var(..) => {}
        }
    }
    let mut found = BTreeSet::from([0, 1, 2, 3]);
    for equation in &definition.equations {
        collect(&equation.lhs, &mut found);
        collect(&equation.rhs, &mut found);
        for condition in equation.requires.iter().chain(&equation.ensures) {
            collect(condition, &mut found);
        }
    }
    // The definition's own literals first.
    let mut ordered = found
        .iter()
        .copied()
        .filter(|value| !(0..=3).contains(value))
        .collect::<Vec<_>>();
    ordered.extend(0..=3);
    ordered
}

/// The ground terms a definition is asked about: the probe's terms, instances of every
/// equation's left-hand side by explored values, applications of the heads and functions to
/// values, and their subterms.
fn queries(
    universe: &mut Universe<'_>,
    values: &BTreeMap<u32, Vec<Id>>,
    seeds: &[Pat],
    rng: &mut Rng,
) -> Vec<Id> {
    let definition = universe.definition;
    let mut roots = Vec::new();
    for seed in seeds {
        let id = universe.ground(seed);
        roots.push(id);
    }
    for equation in &definition.equations {
        let mut variables = BTreeMap::new();
        pattern_variables(&equation.lhs, &mut variables);
        for _ in 0..VALUATIONS_PER_EQUATION {
            let mut valuation = HashMap::new();
            let mut complete = true;
            for (name, sort) in &variables {
                let sort = universe.sort_id(sort);
                let candidates = candidates_of(universe, values, sort);
                if candidates.is_empty() {
                    complete = false;
                    break;
                }
                valuation.insert(name.clone(), *rng.pick(&candidates));
            }
            if complete {
                let instance = instance_of(universe, &equation.lhs, &valuation);
                roots.push(instance);
            }
        }
    }
    for symbol in &definition.symbols {
        if !(symbol.is_head() || symbol.is_function()) || symbol.kind == Kind::Hook {
            continue;
        }
        let symbol_id = universe.symbol_id(&symbol.name);
        for _ in 0..2 {
            let mut arguments = Vec::new();
            for sort in &symbol.arguments {
                let sort = universe.sort_id(sort);
                let candidates = candidates_of(universe, values, sort);
                if candidates.is_empty() {
                    break;
                }
                arguments.push(*rng.pick(&candidates));
            }
            if arguments.len() == symbol.arguments.len() {
                let id = universe.node(Node::App(symbol_id, arguments));
                roots.push(id);
            }
        }
    }
    let mut queries = Vec::new();
    let mut seen = HashSet::new();
    let mut stack = roots;
    stack.reverse();
    while let Some(id) = stack.pop() {
        if id == BOTTOM || !seen.insert(id) {
            continue;
        }
        if matches!(universe.node_of(id), Node::App(..) | Node::List(_)) {
            queries.push(id);
        }
        let mut children = universe.children(id);
        children.reverse();
        stack.extend(children);
    }
    // The seeds first, then a sample of the rest.
    let first = seeds.len().min(queries.len());
    let mut rest = queries.split_off(first);
    while queries.len() < QUERIES && !rest.is_empty() {
        let index = rng.below(rest.len());
        queries.push(rest.swap_remove(index));
    }
    queries
}

/// The ground instance of a left-hand side: an alias `\and(p, X)` is `p`'s instance.
fn instance_of(universe: &mut Universe<'_>, pattern: &Pat, valuation: &HashMap<String, Id>) -> Id {
    let pattern = without_aliases(pattern);
    universe.instantiate(&pattern, valuation)
}

pub(super) fn without_aliases(pattern: &Pat) -> Pat {
    match pattern {
        Pat::As(inner, _, _) => without_aliases(inner),
        Pat::App(name, arguments) => Pat::App(
            name.clone(),
            arguments.iter().map(without_aliases).collect(),
        ),
        Pat::Inj(from, to, inner) => {
            Pat::Inj(from.clone(), to.clone(), Box::new(without_aliases(inner)))
        }
        Pat::List(prefix, rest, suffix) => Pat::List(
            prefix.iter().map(without_aliases).collect(),
            rest.clone(),
            suffix.iter().map(without_aliases).collect(),
        ),
        Pat::Var(..) | Pat::Int(_) => pattern.clone(),
    }
}

/// The oracle's own taint closure (the design's 3.8) from the backend's non-joined pairs:
/// equations are identified by their labels.
pub(super) fn oracle_taint(
    definition: &Definition,
    seeds: impl IntoIterator<Item = usize>,
) -> (BTreeSet<usize>, BTreeSet<String>) {
    let taintable = |name: &str| {
        definition
            .symbols
            .iter()
            .find(|symbol| symbol.name == name)
            .is_some_and(|symbol| !matches!(symbol.kind, Kind::Constructor | Kind::Hook))
    };
    let mut equations = BTreeSet::new();
    let mut symbols = BTreeSet::new();
    let mut queue = seeds.into_iter().collect::<Vec<_>>();
    loop {
        while let Some(index) = queue.pop() {
            if !equations.insert(index) {
                continue;
            }
            let equation = &definition.equations[index];
            let mut mentioned = BTreeSet::new();
            for pattern in [Some(&equation.lhs), Some(&equation.rhs)]
                .into_iter()
                .chain([equation.requires.as_ref(), equation.ensures.as_ref()])
                .flatten()
            {
                symbols_of(pattern, &mut mentioned);
            }
            symbols.extend(mentioned.into_iter().filter(|name| taintable(name)));
            let mut variables = BTreeMap::new();
            pattern_variables(&equation.lhs, &mut variables);
            for sort in variables.values() {
                symbols.extend(observable_heads(definition, sort));
            }
        }
        for (index, equation) in definition.equations.iter().enumerate() {
            if equations.contains(&index) {
                continue;
            }
            let mut mentioned = BTreeSet::new();
            symbols_of(&equation.lhs, &mut mentioned);
            if mentioned.iter().any(|name| symbols.contains(name)) {
                queue.push(index);
            }
        }
        if queue.is_empty() {
            return (equations, symbols);
        }
    }
}

fn symbols_of(pattern: &Pat, into: &mut BTreeSet<String>) {
    match pattern {
        Pat::App(name, arguments) => {
            into.insert(name.clone());
            for argument in arguments {
                symbols_of(argument, into);
            }
        }
        Pat::Inj(_, _, inner) | Pat::As(inner, _, _) => symbols_of(inner, into),
        Pat::List(prefix, _, suffix) => {
            for element in prefix.iter().chain(suffix) {
                symbols_of(element, into);
            }
        }
        Pat::Var(..) | Pat::Int(_) => {}
    }
}

/// The equation heads whose applications can occur inside an element of `sort` in the model of
/// the design's 3.8, as corrected by its "Revision after review 1" (R1.2): the sorts of the
/// subterms are closed under subsorts (an injection's operand), the element sort of lists, and
/// the argument sorts of the symbols that model interprets formally on new arguments:
/// constructors, equation heads, and total functions and `functional` symbols whose result sort
/// has no element in some model (otherwise the model reads such an application by a fixed old
/// element of its sort, and the oracle's total symbols are never injective). A partial
/// function's stuck application is `\bottom`, and a hook's result a literal.
pub(super) fn observable_heads(definition: &Definition, sort: &str) -> BTreeSet<String> {
    let order = definition.sort_order();
    let surely = surely_inhabited(definition);
    let mut reached = BTreeSet::from([sort.to_owned()]);
    let mut stack = vec![sort.to_owned()];
    while let Some(sort) = stack.pop() {
        let mut next = order.get(&sort).cloned().unwrap_or_default();
        if sort == "List" {
            next.push("Int".into());
        }
        for symbol in &definition.symbols {
            let formal = match symbol.kind {
                Kind::Constructor | Kind::Head { .. } => true,
                Kind::Function { total: true } | Kind::Functional => {
                    !surely.contains(&symbol.result)
                }
                Kind::Function { total: false } | Kind::Hook => false,
            };
            if formal && symbol.result == sort {
                next.extend(symbol.arguments.iter().cloned());
            }
        }
        for sort in next {
            if reached.insert(sort.clone()) {
                stack.push(sort);
            }
        }
    }
    definition
        .symbols
        .iter()
        .filter(|symbol| symbol.is_head() && reached.contains(&symbol.result))
        .map(|symbol| symbol.name.clone())
        .collect()
}

/// The sorts with an element in every model: `Int`, `Bool` and `List`, the result sort of a
/// symbol defined on defined arguments (a constructor, or one declared total) whose argument
/// sorts are in the set, and the supersorts of a sort in the set.
pub(super) fn surely_inhabited(definition: &Definition) -> BTreeSet<String> {
    let mut set = BTreeSet::from(["Int".to_owned(), "Bool".to_owned(), "List".to_owned()]);
    loop {
        let before = set.len();
        for symbol in &definition.symbols {
            if symbol.total() && symbol.arguments.iter().all(|sort| set.contains(sort)) {
                set.insert(symbol.result.clone());
            }
        }
        for (sub, sup) in &definition.subsorts {
            if set.contains(sub) {
                set.insert(sup.clone());
            }
        }
        if set.len() == before {
            return set;
        }
    }
}

/// The oracle term of a ground backend term, when it is one the oracle's language writes.
pub(super) fn oracle_term(universe: &mut Universe<'_>, term: &Term) -> Option<Id> {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            let children = arguments
                .iter()
                .map(|argument| oracle_term(universe, argument))
                .collect::<Option<Vec<_>>>()?;
            match symbol.name.as_ref() {
                "listUnit" => Some(universe.node(Node::List(Vec::new()))),
                "listItem" => Some(universe.node(Node::List(children))),
                "listConcat" => {
                    let mut elements = Vec::new();
                    for child in children {
                        let Node::List(items) = universe.node_of(child) else {
                            return None;
                        };
                        elements.extend(items.clone());
                    }
                    Some(universe.node(Node::List(elements)))
                }
                name => {
                    if !universe
                        .definition
                        .symbols
                        .iter()
                        .any(|symbol| symbol.name == name)
                    {
                        return None;
                    }
                    let symbol = universe.symbol_id(name);
                    Some(universe.node(Node::App(symbol, children)))
                }
            }
        }
        TermKind::DomainValue { sort, value } => {
            let text = std::str::from_utf8(value.as_bytes()).ok()?;
            match sort_name(sort)?.as_str() {
                "Int" => Some(universe.int(text.parse().ok()?)),
                "Bool" => Some(universe.boolean(text.parse().ok()?)),
                _ => None,
            }
        }
        TermKind::Injection {
            source,
            target,
            term,
        } => {
            let inner = oracle_term(universe, term)?;
            let (from, to) = (sort_name(source)?, sort_name(target)?);
            let (from, to) = (universe.sort_id(&from), universe.sort_id(&to));
            Some(universe.node(Node::Inj(from, to, inner)))
        }
        TermKind::List { heads, rest, .. } => {
            let mut elements = heads
                .iter()
                .map(|element| oracle_term(universe, element))
                .collect::<Option<Vec<_>>>()?;
            if let Some((middle, tail)) = rest {
                let middle = oracle_term(universe, middle)?;
                let Node::List(items) = universe.node_of(middle).clone() else {
                    return None;
                };
                elements.extend(items);
                for element in tail {
                    elements.push(oracle_term(universe, element)?);
                }
            }
            Some(universe.node(Node::List(elements)))
        }
        TermKind::Variable(_) | TermKind::And(..) | TermKind::Map { .. } | TermKind::Set { .. } => {
            None
        }
    }
}

/// The oracle's name of a backend sort (`SortA{}` is `A`).
pub(super) fn sort_name(sort: &Sort) -> Option<String> {
    match sort {
        Sort::Application { name, arguments } if arguments.is_empty() => {
            name.strip_prefix("Sort").map(str::to_owned)
        }
        _ => None,
    }
}

/// How long one backend call may take: the backend evaluates terms the oracle shows terminating
/// under `->E`, but its own evaluation may apply an equation to an argument that is not yet a
/// normal form (a division by zero kept as an argument and re-bound, `h(X, I) = h(f(I), 1 /Int
/// I)`), which need not end. A stopped call claims nothing.
const BACKEND_SECONDS: u64 = 2;

pub(super) fn deadline() -> crate::stop::DeadlineGuard {
    let limit = std::time::Duration::from_secs(BACKEND_SECONDS);
    crate::stop::arm_deadline(
        std::time::Instant::now() + limit,
        crate::timeout::StepTimeoutMode::Manual(limit),
    )
}

/// The claims the backend makes about one ground term or generalization.
struct Claims {
    token: bool,
    /// `\ceil` simplified to `\top`; `None` when it was not asked.
    ceil_top: Option<bool>,
}

fn claims(
    backend: &BackendDefinition,
    kore: &str,
    sort: &str,
    ask_ceil: bool,
) -> Result<Claims, String> {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let _deadline = deadline();
        let term = backend
            .internalize_term(&parse_pattern(kore).expect("the term parses"), &[])
            .map_err(|error| format!("{kore} does not internalize: {error:?}"))?;
        let token = backend.instance_normal(&term).is_some();
        let ceil_top = if ask_ceil {
            let ceil = format!(r"\ceil{{Sort{sort}{{}}, Sort{sort}{{}}}}({kore})");
            let syntax = parse_pattern(&ceil).expect("the query parses");
            let (predicate, _) = backend
                .admit_unverified(&syntax, &[])
                .internalize_predicate()
                .expect("the query internalizes");
            let simplified = simplify_predicate_with_solver(
                backend,
                &predicate,
                &[],
                SimplificationOptions {
                    max_iterations: 16,
                    ..SimplificationOptions::default()
                },
                &NoSolver,
            );
            Some(match simplified {
                Ok(Ok(Predicate::True)) => true,
                Ok(_) => false,
                // A stop (the deadline, the stack guard) claims nothing.
                Err(stop) => {
                    stop.into_cause();
                    false
                }
            })
        } else {
            None
        };
        Ok(Claims { token, ceil_top })
    }));
    outcome.unwrap_or_else(|panic| {
        Err(format!(
            "{kore}: the backend panicked: {}",
            panic_text(&*panic)
        ))
    })
}

pub(super) fn panic_text(panic: &(dyn std::any::Any + Send)) -> String {
    panic
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_owned()))
        .unwrap_or_default()
}

/// The simplifier's result for a ground term, if it gives one.
fn simplified(backend: &BackendDefinition, kore: &str) -> Option<Term> {
    catch_unwind(AssertUnwindSafe(|| {
        let _deadline = deadline();
        let term = backend
            .internalize_term(&parse_pattern(kore).expect("the term parses"), &[])
            .ok()?;
        let result = match simplify(
            backend,
            &term,
            SimplificationOptions {
                max_iterations: 64,
                ..SimplificationOptions::default()
            },
        ) {
            Ok(result) => result.ok()?,
            Err(stop) => {
                stop.into_cause();
                return None;
            }
        };
        // A result with conditions (an `ensures`, a definedness obligation) is not the value.
        (result.constraints().is_empty() && result.undefined_term.is_none()).then_some(result.term)
    }))
    .ok()
    .flatten()
}

/// The subterms of `term` that carry the certificate and are equation-head applications.
fn certified_heads(backend: &BackendDefinition, term: &Term, into: &mut Vec<Term>) {
    if let TermKind::Application { symbol, .. } = term.kind()
        && backend.symbols().get(&symbol.name).is_some_and(|symbol| {
            symbol.attributes.head_role() == crate::term::HeadRole::EquationHead
        })
        && certified_ground_normal_form(term)
    {
        into.push(term.clone());
    }
    for child in subterms(term) {
        certified_heads(backend, &child, into);
    }
}

/// The immediate subterms of a backend term.
fn subterms(term: &Term) -> Vec<Term> {
    match term.kind() {
        TermKind::Application { arguments, .. } => arguments.clone(),
        TermKind::Injection { term, .. } => vec![term.clone()],
        TermKind::And(left, right) => vec![left.clone(), right.clone()],
        TermKind::List { heads, rest, .. } => {
            let mut children = heads.clone();
            if let Some((middle, tail)) = rest {
                children.push(middle.clone());
                children.extend(tail.iter().cloned());
            }
            children
        }
        TermKind::Map { entries, rest, .. } => entries
            .iter()
            .flat_map(|(key, value)| [key.clone(), value.clone()])
            .chain(rest.iter().cloned())
            .collect(),
        TermKind::Set { elements, rest, .. } => elements
            .iter()
            .cloned()
            .chain(rest.iter().cloned())
            .collect(),
        TermKind::DomainValue { .. } | TermKind::Variable(_) => Vec::new(),
    }
}

/// The standing of a query with respect to the taint set.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Standing {
    /// Accepted definition, or an untainted term whose evaluation applies only untainted
    /// equations: its claims must agree with its normal form.
    Model,
    /// The term holds an application of a tainted symbol: no claim.
    Tainted,
    /// Untainted, but its evaluation applies a tainted equation: not checked.
    Unchecked,
}

/// Runs every check on `definition`, seeded with `seeds` and asked about `probes` (whose
/// verdicts are returned).
#[allow(
    clippy::too_many_lines,
    reason = "one pass over the claims of one definition"
)]
pub(super) fn check_definition(
    label: &str,
    definition: &Definition,
    seeds: &[Pat],
    probes: &[Pat],
    rng: &mut Rng,
) -> (Tally, Verdict) {
    let mut tally = Tally {
        definitions: 1,
        ..Tally::default()
    };
    for class in classes(definition) {
        tally.classes.insert(class, 1);
    }
    let mut verdict = Verdict::default();
    let verbose = std::env::var_os("KRUST_DEFINEDNESS_ORACLE_VERBOSE").is_some();
    if std::env::var_os("KRUST_DEFINEDNESS_ORACLE_PROGRESS").is_some() {
        eprintln!("{label}");
    }
    if std::env::var_os("KRUST_DEFINEDNESS_ORACLE_KORE").is_some() {
        eprintln!("{label}:\n{}", definition.kore());
    }
    let describe = || format!("  definition:\n{}", describe(definition));
    let backend = match backend(definition) {
        Ok(backend) => backend,
        Err(error) => {
            tally.rejected = 1;
            tally
                .failures
                .push(format!("{label}: rejected: {error}\n{}", describe()));
            return (tally, verdict);
        }
    };
    // V9: the load's verdict (`CheckScope::Gate`) and the full check's admit the same claims and
    // warn about the same pairs. The oracle's own expectations (acceptance, V4's one normal form,
    // the tainted set of V6) are statements about the full check, so they are read from its
    // verdict; the claims are read from the loaded definition below.
    let full = backend.value_claims_in_scope(crate::confluence::CheckScope::All);
    tally.with_skipped_pair += usize::from(backend.value_claims().counts().skipped > 0);
    for difference in backend.value_claims().claim_differences(&full, &backend) {
        tally.failures.push(format!(
            "{label}: {SCOPES}: the load's scope and the full check differ: {difference}\n{}",
            describe()
        ));
    }
    // The memo of condition simplifications changes no verdict and no count but its hits.
    let unmemoized = backend.value_claims_checked(
        crate::confluence::CheckScope::All,
        crate::confluence::ConditionMemo::Off,
    );
    for difference in full
        .verdict_differences(&unmemoized)
        .into_iter()
        .chain(memo_count_difference(&full, &unmemoized))
    {
        tally.failures.push(format!(
            "{label}: {MEMO}: the full check with and without the memo differ: {difference}\n{}",
            describe()
        ));
    }
    tally.memo_hits += full.counts().condition_memo_hits;
    tally.memo_conditions += full.counts().simplifier_calls;
    let value_claims = &full;
    let has_head = definition.symbols.iter().any(|symbol| symbol.is_head());
    // Without an equation head the check stops after the precondition rows: it accepts nothing.
    verdict.accepted =
        has_head && value_claims.unjoined().is_empty() && value_claims.violations().is_empty();
    verdict.tainted = value_claims
        .tainted_symbols()
        .iter()
        .map(|name| name.to_string())
        .collect();
    tally.accepted = usize::from(verdict.accepted);
    let heads = definition
        .symbols
        .iter()
        .filter(|symbol| symbol.is_head())
        .map(|symbol| symbol.name.clone())
        .collect::<BTreeSet<_>>();
    let tainted_heads = heads.intersection(&verdict.tainted).count();
    tally.partially_tainted = usize::from(tainted_heads > 0 && tainted_heads < heads.len());

    for pair in value_claims.unjoined() {
        let reason = match &pair.reason {
            crate::confluence::UnjoinedReason::Unresolved(shape) => format!("unresolved {shape}"),
            reason => format!("{reason:?}"),
        };
        *tally.reasons.entry(reason).or_default() += 1;
    }
    // V6 (a): the oracle's closure from the reported pairs.
    let mut seeds_of_taint = BTreeSet::new();
    for pair in value_claims.unjoined() {
        for rule in [&pair.first, &pair.second] {
            match equation_index(rule.attributes.label.as_deref()) {
                Some(index) => {
                    seeds_of_taint.insert(index);
                }
                None => tally.failures.push(format!(
                    "{label}: a reported pair names an equation without the oracle's label\n{}",
                    describe()
                )),
            }
        }
    }
    let (tainted_equations, oracle_tainted) = oracle_taint(definition, seeds_of_taint);
    if value_claims.violations().is_empty() && oracle_tainted != verdict.tainted {
        tally.failures.push(format!(
            "{label}: the backend taints {:?}, the oracle's closure of the same pairs {:?}\n{}",
            verdict.tainted,
            oracle_tainted,
            describe()
        ));
    }
    let tainted_mask = tainted_equations
        .iter()
        .fold(0u128, |mask, index| mask | (1u128 << index));

    let mut universe = Universe::new(definition);
    let values = values(&mut universe, rng);
    let mut asked = queries(&mut universe, &values, seeds, rng);
    let probe_ids = probes
        .iter()
        .map(|probe| universe.ground(probe))
        .collect::<Vec<_>>();
    for id in &probe_ids {
        if !asked.contains(id) {
            asked.insert(0, *id);
        }
    }
    // P2: a definition that reaches a total symbol with no value on defined arguments is
    // outside the contract.
    for id in asked.clone() {
        let mut subterms = vec![id];
        while let Some(term) = subterms.pop() {
            if universe.violates_totality(term) {
                tally.outside_totality = 1;
            }
            subterms.extend(universe.children(term));
        }
    }
    // V6 (d): what every model makes undefined, from the axioms alone.
    // Its roots are the queries, the seeds, and instances of every left-hand side by explored
    // values, so that an equation instance showing the definition has no model is seen even when
    // no query holds it.
    let mut forced_roots = asked.clone();
    for seed in seeds {
        forced_roots.push(universe.ground(seed));
    }
    for equation in &definition.equations {
        let mut variables = BTreeMap::new();
        pattern_variables(&equation.lhs, &mut variables);
        let candidates = variables
            .values()
            .map(|sort| {
                let sort = universe.sort_id(sort);
                candidates_of(&mut universe, &values, sort)
            })
            .collect::<Vec<_>>();
        if candidates.iter().any(Vec::is_empty) {
            continue;
        }
        for offset in 0..FORCED_INSTANCES {
            let valuation = variables
                .keys()
                .zip(&candidates)
                .enumerate()
                .map(|(index, (name, candidates))| {
                    (
                        name.clone(),
                        candidates[(offset + index) % candidates.len()],
                    )
                })
                .collect::<HashMap<_, _>>();
            forced_roots.push(instance_of(&mut universe, &equation.lhs, &valuation));
        }
    }
    // The same P2 test on these roots: an instance there can reach a total symbol with no value
    // on normal forms that no query holds.
    for id in forced_roots.clone() {
        let mut subterms = vec![id];
        while let Some(term) = subterms.pop() {
            if universe.violates_totality(term) {
                tally.outside_totality = 1;
            }
            subterms.extend(universe.children(term));
        }
    }
    let forced = super::forced::derive(&mut universe, &forced_roots);
    if forced.inconsistent.is_some() {
        tally.without_model = 1;
    }
    let forced_check = forced.inconsistent.is_none();
    // The contract's claims are those on terms the backend's own verdict leaves untainted, whose
    // evaluation applies no equation rooted at a symbol it taints: on a non-joined pair the
    // evaluator may take either side, so a `\ceil` discharged through such an equation is an
    // evaluation, not a value claim. Read from the backend's taint set, so that a closure rule
    // that misses a class does not hide its claims here.
    let backend_tainted = verdict
        .tainted
        .iter()
        .map(|name| universe.symbol_id(name))
        .collect::<HashSet<_>>();
    let tainted_roots = definition
        .equations
        .iter()
        .enumerate()
        .filter(|(_, equation)| verdict.tainted.contains(equation.root()))
        .fold(0u128, |mask, (index, _)| mask | (1u128 << index));
    // The evaluator's documented limit (`docs/compatibility.md`, "Anywhere rules"): an equation
    // whose left-hand side holds a declared function's application below its root is applied
    // before that application is evaluated, so a `\ceil` discharged through it rests on an
    // evaluation `->E` does not take, not on a value claim. Terms holding the roots of such
    // equations are not read for `\ceil` or marker claims by V6 (d).
    let below_root_roots = below_root_roots(definition, &universe);
    let claimed_untainted = |universe: &mut Universe<'_>, id: Id| {
        let mut symbols = HashSet::new();
        universe.symbols_in(id, &mut symbols);
        symbols.is_disjoint(&backend_tainted) && universe.normalize(id).applied & tainted_roots == 0
    };
    let tainted_symbols = oracle_tainted
        .iter()
        .map(|name| universe.symbol_id(name))
        .collect::<HashSet<_>>();
    let accepted = verdict.accepted;
    let standing = |universe: &mut Universe<'_>, id: Id| -> Standing {
        let mut symbols = HashSet::new();
        universe.symbols_in(id, &mut symbols);
        if symbols
            .iter()
            .any(|symbol| tainted_symbols.contains(symbol))
        {
            return Standing::Tainted;
        }
        let normal = universe.normalize(id);
        if accepted || normal.applied & tainted_mask == 0 {
            Standing::Model
        } else {
            Standing::Unchecked
        }
    };
    let mut results = Vec::new();
    // The claims' failures, from here on, are dropped for a definition found outside P2 by the
    // end: its `total` declarations are false, and the contract makes no promise there.
    let claim_failures_from = tally.failures.len();
    for id in asked.clone() {
        tally.queries += 1;
        let normal = universe.normalize(id);
        if !normal.complete {
            tally.nonterminating += 1;
            continue;
        }
        if tally.outside_totality > 0 && !probe_ids.contains(&id) {
            continue;
        }
        let place = standing(&mut universe, id);
        let shown = universe.show(id);
        if verbose {
            eprintln!(
                "{label}: {shown} -> {:?} ({place:?})",
                normal
                    .forms
                    .iter()
                    .map(|form| universe.show(*form))
                    .collect::<Vec<_>>()
            );
        }
        // V4, and the untainted fragment of V6 (b): one normal form.
        if place == Standing::Model && normal.forms.len() > 1 && !has_head {
            // No claim reads the equations of a definition without heads; the claims on a term
            // with two normal forms are not checked against either.
            continue;
        }
        if place == Standing::Model && normal.forms.len() > 1 && tally.outside_totality == 0 {
            tally.failures.push(format!(
                "{label}: {shown} has the normal forms {:?}{}\n{}",
                normal
                    .forms
                    .iter()
                    .map(|form| universe.show(*form))
                    .collect::<Vec<_>>(),
                if verdict.accepted {
                    " in an accepted definition"
                } else {
                    " in the untainted fragment"
                },
                describe()
            ));
            continue;
        }
        let sort = universe.sort_name(universe.sort_of(id)).to_owned();
        let kore = universe.kore(id, None);
        // The backend's evaluation of the query. Where it ends in a certified value other than
        // the query's normal form under `->E`, the evaluator took a step `->E` does not (a
        // function equation whose left-hand side holds a function application below its root
        // applies before that application is evaluated): a divergence of evaluation, not of a
        // value claim, counted and reported, and the `\ceil` discharge that rests on it is not
        // read as a claim.
        let evaluation = simplified(&backend, &kore);
        let mut divergent = false;
        if let Some(result) = &evaluation
            && place == Standing::Model
            && tally.outside_totality == 0
            && let Some(result_id) = oracle_term(&mut universe, result)
            && universe.normalize(result_id).forms != normal.forms
        {
            divergent = true;
            tally.divergent += 1;
            if tally.divergences.len() < 5 {
                tally.divergences.push(format!(
                    "{label}: {shown} evaluates to {}, under ->E to {:?}",
                    universe.show(result_id),
                    normal
                        .forms
                        .iter()
                        .map(|form| universe.show(*form))
                        .collect::<Vec<_>>(),
                ));
            }
        }
        let found = match claims(&backend, &kore, &sort, true) {
            Ok(found) => found,
            Err(failure) => {
                tally
                    .failures
                    .push(format!("{label}: {failure}\n{}", describe()));
                continue;
            }
        };
        if probe_ids.contains(&id) {
            verdict
                .probes
                .push((found.ceil_top != Some(true), found.token));
        }
        let defined = !normal.forms.contains(&BOTTOM);
        let normal_form = universe.is_normal_form(id);
        let term = backend
            .internalize_term(&parse_pattern(&kore).expect("the term parses"), &[])
            .expect("the term internalizes");
        // S5: the marker's claim that an irreducible application is defined.
        let marker_claim = matches!(universe.node_of(id), Node::App(..))
            && backend.irreducible_application_is_defined(&term);
        let mut failed = Vec::new();
        let mut fail = |failure: String| failed.push(failure);
        // V6 (d): no claim on an untainted term that every model makes undefined.
        if forced_check && forced.undefined(id) {
            tally.forced_undefined += 1;
        }
        if forced_check
            && forced.undefined(id)
            && tally.outside_totality == 0
            && claimed_untainted(&mut universe, id)
        {
            let mut symbols = HashSet::new();
            universe.symbols_in(id, &mut symbols);
            let evaluated_below_root = !symbols.is_disjoint(&below_root_roots);
            let claimed = [
                (found.token, "instance-normal"),
                (
                    marker_claim && !evaluated_below_root,
                    "an irreducible defined application",
                ),
                (
                    found.ceil_top == Some(true) && !divergent && !evaluated_below_root,
                    "defined (its \\ceil is discharged)",
                ),
            ];
            for (made, what) in claimed {
                if made {
                    fail(format!(
                        "{FORCED}: every model makes {shown} undefined, but it is called {what}"
                    ));
                }
            }
        }
        match place {
            Standing::Model if tally.outside_totality == 0 => {
                if found.token {
                    tally.tokens += 1;
                    if !normal_form {
                        fail(format!("{shown} is instance-normal but not a normal form"));
                    }
                }
                if marker_claim {
                    tally.markers += 1;
                    if !normal_form {
                        fail(format!(
                            "{shown} is called an irreducible defined application but its normal forms are {:?}",
                            normal
                                .forms
                                .iter()
                                .map(|form| universe.show(*form))
                                .collect::<Vec<_>>()
                        ));
                    }
                }
                if found.ceil_top == Some(true) && !divergent {
                    tally.ceilings += 1;
                    if !defined {
                        fail(format!(
                            "\\ceil({shown}) is discharged but {shown} is undefined"
                        ));
                    }
                }
            }
            Standing::Tainted => {
                if found.token {
                    fail(format!(
                        "{shown} holds a tainted application and is instance-normal"
                    ));
                } else {
                    tally.withheld += 1;
                }
                if let Node::App(symbol, _) = universe.node_of(id).clone()
                    && tainted_symbols.contains(&symbol)
                    && marker_claim
                {
                    fail(format!("{shown} has a tainted root and is called defined"));
                }
            }
            Standing::Model | Standing::Unchecked => {}
        }
        for failure in failed {
            tally
                .failures
                .push(format!("{label}: {failure}\n{}", describe()));
        }
        // V6 (d) on generalizations: a claim on the query with a subterm defined in every model
        // replaced by a variable holds, in particular, at that subterm.
        if forced_check && forced.undefined(id) && tally.outside_totality == 0 {
            forced_generalizations(
                label,
                &backend,
                &mut universe,
                (&forced, &backend_tainted),
                id,
                &mut tally,
                &describe,
            );
        }
        // Certificates.
        if let Some(result) = evaluation {
            let mut certified = Vec::new();
            certified_heads(&backend, &result, &mut certified);
            for term in certified {
                let Some(certified_id) = oracle_term(&mut universe, &term) else {
                    continue;
                };
                let certified_place = standing(&mut universe, certified_id);
                if forced_check
                    && forced.undefined(certified_id)
                    && tally.outside_totality == 0
                    && claimed_untainted(&mut universe, certified_id)
                {
                    let text = universe.show(certified_id);
                    tally.failures.push(format!(
                        "{label}: {FORCED}: every model makes {text} undefined, but it carries the certificate\n{}",
                        describe()
                    ));
                }
                match certified_place {
                    Standing::Tainted => {
                        let text = universe.show(certified_id);
                        tally.failures.push(format!(
                            "{label}: {text} holds a tainted application and carries the certificate\n{}",
                            describe()
                        ));
                    }
                    Standing::Model if tally.outside_totality == 0 => {
                        tally.certificates += 1;
                        if !universe.is_normal_form(certified_id) {
                            let text = universe.show(certified_id);
                            tally.failures.push(format!(
                                "{label}: {text} carries the certificate but is not a normal form\n{}",
                                describe()
                            ));
                        }
                    }
                    Standing::Model | Standing::Unchecked => {}
                }
            }
            if place == Standing::Model
                && certified_ground_normal_form(&result)
                && let Some(result_id) = oracle_term(&mut universe, &result)
            {
                results.push((result_id, result));
            }
        }
        // Generalizations: a constructor or literal subterm replaced by a variable.
        if tally.outside_totality == 0 {
            generalize(
                label,
                &backend,
                &mut universe,
                &values,
                id,
                &standing,
                &mut tally,
                &describe,
            );
        }
    }
    // Apartness of certified results of the same sort.
    for (index, (left_id, left)) in results.iter().enumerate() {
        for (right_id, right) in &results[index + 1..] {
            if left.sort() != right.sort() {
                continue;
            }
            let apart = catch_unwind(AssertUnwindSafe(|| {
                crate::definedness::elements_are_apart(&backend, left, right)
            }))
            .unwrap_or(false);
            if apart {
                tally.apartness += 1;
                let (left_normal, right_normal) =
                    (universe.normalize(*left_id), universe.normalize(*right_id));
                if left_normal.complete && left_normal.forms == right_normal.forms {
                    tally.failures.push(format!(
                        "{label}: {} and {} are called apart but have the same normal form\n{}",
                        universe.show(*left_id),
                        universe.show(*right_id),
                        describe()
                    ));
                }
            }
        }
    }
    if tally.outside_totality > 0 {
        tally.failures.truncate(claim_failures_from);
    }
    (tally, verdict)
}

/// The roots of the equations whose left-hand side holds a declared function's application
/// below its root.
fn below_root_roots(definition: &Definition, universe: &Universe<'_>) -> HashSet<u32> {
    fn holds_function(pattern: &Pat, definition: &Definition) -> bool {
        match pattern {
            Pat::App(name, arguments) => {
                definition.symbols.iter().any(|symbol| {
                    symbol.name == *name && matches!(symbol.kind, Kind::Function { .. })
                }) || arguments
                    .iter()
                    .any(|argument| holds_function(argument, definition))
            }
            Pat::Inj(_, _, inner) | Pat::As(inner, _, _) => holds_function(inner, definition),
            Pat::List(prefix, _, suffix) => prefix
                .iter()
                .chain(suffix)
                .any(|element| holds_function(element, definition)),
            Pat::Var(..) | Pat::Int(_) => false,
        }
    }
    definition
        .equations
        .iter()
        .filter(|equation| match &equation.lhs {
            Pat::App(_, arguments) => arguments
                .iter()
                .any(|argument| holds_function(argument, definition)),
            _ => false,
        })
        .map(|equation| universe.symbol_id(equation.root()))
        .collect()
}

/// V6 (d) on generalizations of the query `id`, which every model makes undefined: for each of
/// its proper subterms that every model makes defined (up to three), the query with that subterm
/// replaced by a variable, when the backend's verdict taints none of its symbols, must get no
/// claim that holds for every element, since the subterm is one and the instance is undefined.
fn forced_generalizations(
    label: &str,
    backend: &BackendDefinition,
    universe: &mut Universe<'_>,
    (forced, backend_tainted): (&super::forced::Forced, &HashSet<u32>),
    id: Id,
    tally: &mut Tally,
    describe: &dyn Fn() -> String,
) {
    let mut holes = Vec::new();
    let mut stack = universe.children(id);
    while let Some(subterm) = stack.pop() {
        if forced.defined(subterm) && !holes.contains(&subterm) {
            holes.push(subterm);
        } else {
            stack.extend(universe.children(subterm));
        }
    }
    holes.truncate(3);
    for hole in holes {
        // The generalization is a claim when no symbol of it (the query without the hole) is
        // tainted by the backend's verdict: then every equation its evaluation can apply is
        // rooted at an untainted symbol.
        let mut symbols = HashSet::new();
        let mut stack = vec![id];
        while let Some(subterm) = stack.pop() {
            if subterm == hole {
                continue;
            }
            if let Node::App(symbol, _) = universe.node_of(subterm) {
                symbols.insert(*symbol);
            }
            stack.extend(universe.children(subterm));
        }
        if !symbols.is_disjoint(backend_tainted) {
            continue;
        }
        let evaluated_below_root =
            !symbols.is_disjoint(&below_root_roots(universe.definition, universe));
        let sort_name = universe.sort_name(universe.sort_of(hole)).to_owned();
        let variable = format!("VarForced:Sort{sort_name}{{}}");
        let kore = universe.kore(id, Some((hole, &variable)));
        let result_sort = universe.sort_name(universe.sort_of(id)).to_owned();
        let Ok(found) = claims(backend, &kore, &result_sort, true) else {
            continue;
        };
        if found.token || (found.ceil_top == Some(true) && !evaluated_below_root) {
            tally.failures.push(format!(
                "{label}: {FORCED}: every model makes {} undefined, but {kore} is called {} for every element\n{}",
                universe.show(id),
                if found.token { "instance-normal" } else { "defined" },
                describe()
            ));
        }
    }
}

/// Checks the claims on the generalizations of `id`: each subterm that is a constructor
/// application or a literal, replaced by a variable of its sort, whose claims must hold on every
/// explored instance.
#[allow(clippy::too_many_arguments, reason = "the context of one query")]
fn generalize(
    label: &str,
    backend: &BackendDefinition,
    universe: &mut Universe<'_>,
    values: &BTreeMap<u32, Vec<Id>>,
    id: Id,
    standing: &dyn Fn(&mut Universe<'_>, Id) -> Standing,
    tally: &mut Tally,
    describe: &dyn Fn() -> String,
) {
    let Node::App(symbol, _) = universe.node_of(id).clone() else {
        return;
    };
    if !universe.definition.symbols[symbol as usize].is_head() {
        return;
    }
    let mut holes = Vec::new();
    let mut stack = universe.children(id);
    while let Some(subterm) = stack.pop() {
        match universe.node_of(subterm).clone() {
            Node::App(inner, _) => {
                if universe.definition.symbols[inner as usize].kind == Kind::Constructor {
                    holes.push(subterm);
                }
                stack.extend(universe.children(subterm));
            }
            Node::Int(_) => holes.push(subterm),
            _ => stack.extend(universe.children(subterm)),
        }
    }
    holes.truncate(2);
    for hole in holes {
        let sort = universe.sort_of(hole);
        let sort_name = universe.sort_name(sort).to_owned();
        let variable = format!("VarGen:Sort{sort_name}{{}}");
        let kore = universe.kore(id, Some((hole, &variable)));
        let result_sort = universe.sort_name(universe.sort_of(id)).to_owned();
        let found = match claims(backend, &kore, &result_sort, true) {
            Ok(found) => found,
            Err(failure) => {
                tally
                    .failures
                    .push(format!("{label}: {failure}\n{}", describe()));
                continue;
            }
        };
        if !found.token && found.ceil_top != Some(true) {
            continue;
        }
        let instances = candidates_of(universe, values, sort)
            .into_iter()
            .filter(|value| universe.sort_of(*value) == sort)
            .collect::<Vec<_>>();
        let mut checked = false;
        for value in instances {
            let instance = replace(universe, id, hole, value);
            let normal = universe.normalize(instance);
            if !normal.complete {
                continue;
            }
            // An instance at which a total symbol is undefined on defined arguments puts the
            // definition outside P2, where its `total` declarations are false.
            let mut subterms = vec![instance];
            let mut outside = false;
            while let Some(subterm) = subterms.pop() {
                outside |= universe.violates_totality(subterm);
                subterms.extend(universe.children(subterm));
            }
            if outside {
                tally.outside_totality = 1;
                continue;
            }
            // An instance by a value holding a tainted application is an instance by an element
            // the oracle does not know in the model the claim is about: not checked.
            match standing(universe, instance) {
                Standing::Model => {
                    checked = true;
                    if found.token && !universe.is_normal_form(instance) {
                        tally.failures.push(format!(
                            "{label}: {kore} is instance-normal but its instance {} is not a normal form\n{}",
                            universe.show(instance),
                            describe()
                        ));
                    }
                    if found.ceil_top == Some(true) && normal.forms.contains(&BOTTOM) {
                        tally.failures.push(format!(
                            "{label}: \\ceil({kore}) is discharged but its instance {} is undefined\n{}",
                            universe.show(instance),
                            describe()
                        ));
                    }
                }
                Standing::Tainted | Standing::Unchecked => {}
            }
        }
        tally.generalizations += usize::from(checked);
    }
}

/// `id` with every occurrence of `hole` replaced by `value`.
fn replace(universe: &mut Universe<'_>, id: Id, hole: Id, value: Id) -> Id {
    if id == hole {
        return value;
    }
    match universe.node_of(id).clone() {
        Node::App(symbol, children) => {
            let children = children
                .into_iter()
                .map(|child| replace(universe, child, hole, value))
                .collect();
            universe.node(Node::App(symbol, children))
        }
        Node::Inj(from, to, child) => {
            let child = replace(universe, child, hole, value);
            universe.node(Node::Inj(from, to, child))
        }
        Node::List(children) => {
            let children = children
                .into_iter()
                .map(|child| replace(universe, child, hole, value))
                .collect();
            universe.node(Node::List(children))
        }
        Node::Bottom | Node::Int(_) | Node::Bool(_) => id,
    }
}

pub(super) fn describe(definition: &Definition) -> String {
    let mut text = String::new();
    for symbol in &definition.symbols {
        if symbol.kind == Kind::Hook {
            continue;
        }
        let kind = match symbol.kind {
            Kind::Constructor => "constructor".to_owned(),
            Kind::Head {
                value_production,
                total,
            } => format!(
                "head{}{}",
                if value_production {
                    " value-production"
                } else {
                    ""
                },
                if total { " total" } else { "" }
            ),
            Kind::Function { total } => format!("function{}", if total { " total" } else { "" }),
            Kind::Functional => "functional".to_owned(),
            Kind::Hook => unreachable!(),
        };
        writeln!(
            text,
            "    {kind} {}({}) : {}",
            symbol.name,
            symbol.arguments.join(", "),
            symbol.result
        )
        .unwrap();
    }
    for (sub, sup) in &definition.subsorts {
        writeln!(text, "    {sub} < {sup}").unwrap();
    }
    for (index, equation) in definition.equations.iter().enumerate() {
        let mut line = format!(
            "    eq{index}: {} = {}",
            show(&equation.lhs),
            show(&equation.rhs)
        );
        if let Some(requires) = &equation.requires {
            write!(line, " requires {}", show(requires)).unwrap();
        }
        if let Some(ensures) = &equation.ensures {
            write!(line, " ensures {}", show(ensures)).unwrap();
        }
        if equation.priority != super::language::DEFAULT_PRIORITY {
            write!(line, " [priority {}]", equation.priority).unwrap();
        }
        if equation.overload.is_some() {
            line.push_str(" [overload]");
        }
        writeln!(text, "{line}").unwrap();
    }
    text
}

pub(super) fn show(pattern: &Pat) -> String {
    match pattern {
        Pat::Var(name, _) => name.clone(),
        Pat::Int(value) => value.to_string(),
        Pat::App(name, arguments) if arguments.is_empty() => name.clone(),
        Pat::App(name, arguments) => format!(
            "{name}({})",
            arguments.iter().map(show).collect::<Vec<_>>().join(", ")
        ),
        Pat::Inj(from, to, inner) => format!("inj{{{from}, {to}}}({})", show(inner)),
        Pat::As(inner, name, _) => format!("{}#{name}", show(inner)),
        Pat::List(prefix, rest, suffix) => {
            let mut parts = prefix.iter().map(show).collect::<Vec<_>>();
            if let Some(rest) = rest {
                parts.push(format!("{rest}.."));
            }
            parts.extend(suffix.iter().map(show));
            format!("[{}]", parts.join(", "))
        }
    }
}
