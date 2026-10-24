//! The checks of one definition that read the backend's verdicts against each other, and the
//! oracle's exploration of the ground terms around the reviewers' probes: V9 (the load's scope
//! and the full check admit the same claims and warn about the same pairs), the memo (the full
//! check with and without its memo of condition simplifications reaches the same verdict), and
//! each probe's `\ceil` obligation and token, with the preconditions P0 and P2 measured by the
//! oracle's evaluator, and the constants check (`M+`: the oracle's surely-inhabited sorts are the
//! backend's, and a definition the full check accepts has the model `D+` with the verdict's
//! witness equations, [`junk_check`], which are well formed and have no tainted head,
//! [`witness_failures`]). The value claims themselves are judged against the axioms by
//! [`super::axioms`].

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::Write as _,
    panic::{AssertUnwindSafe, catch_unwind},
};

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::{
    Rng,
    engine::{BOTTOM, Id, Node, Universe},
    language::{Definition, Equation, JUNK_PREFIX, Kind, Pat, junk_constant, pattern_variables},
};
use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    simplify::{SimplificationOptions, simplify_predicate_with_solver},
    smt::NoSolver,
    term::{Sort, SortNode, Term, TermKind},
};

/// Ground terms explored around a probe definition.
const QUERIES: usize = 40;

/// The tag of V9's failures: the load's scope and the full check differ on a claim or a warning.
pub(super) const SCOPES: &str = "V9";

/// The tag of the memo's failures: the full check with and without its memo of condition
/// simplifications differ in a verdict or a count other than the memo's own work.
pub(super) const MEMO: &str = "memo";

/// Where the counts of `on`, a verdict computed with the memo of condition simplifications, and
/// `off`, the same check's without it, differ beyond the memo's own work, if anywhere.
pub(super) fn memo_count_difference(
    on: &crate::confluence::ValueClaims,
    off: &crate::confluence::ValueClaims,
) -> Option<String> {
    (on.counts().without_memo_work() != off.counts().without_memo_work()).then(|| {
        format!(
            "counts with the memo {:?} against without {:?}",
            on.counts(),
            off.counts()
        )
    })
}

/// Values per sort, and instances of each left-hand side among the explored terms.
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
    /// An equation head written as a hooked symbol ([`Definition::hooked_heads`]).
    HookedHead,
}

impl Class {
    pub(super) const ALL: [Self; 13] = [
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
        Self::HookedHead,
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
    pub(super) classes: BTreeMap<Class, usize>,
    /// The reasons of the non-joined pairs, counted.
    pub(super) reasons: BTreeMap<String, usize>,
    /// The conditions the full check simplified, and those of them the memo answered.
    pub(super) memo_conditions: usize,
    pub(super) memo_hits: usize,
    /// Definitions whose load skipped a pair the full check classifies (`CheckCounts::skipped`):
    /// those on which V9 compares the two scopes where they could differ.
    pub(super) with_skipped_pair: usize,
    /// The axiom instances the constants check judged in `D+` ([`junk_check`]), those of them
    /// over values that hold a constant, and the terms free of constants it evaluated in both
    /// `D+` and the definition.
    pub(super) junk_instances: usize,
    pub(super) junk_constant_instances: usize,
    pub(super) junk_agreements: usize,
    /// The definitions the constants check judged with witness equations
    /// (`ValueClaims::witnesses`) in `D+`, and the instances of witness equations it judged.
    pub(super) junk_witnessed: usize,
    pub(super) junk_witness_instances: usize,
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
        self.memo_conditions += other.memo_conditions;
        self.memo_hits += other.memo_hits;
        self.with_skipped_pair += other.with_skipped_pair;
        self.junk_instances += other.junk_instances;
        self.junk_constant_instances += other.junk_constant_instances;
        self.junk_agreements += other.junk_agreements;
        self.junk_witnessed += other.junk_witnessed;
        self.junk_witness_instances += other.junk_witness_instances;
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
            "{name}: {} definitions ({} rejected, {} accepted, {} partially tainted, {} outside P2), {} probe queries explored ({} outside P0); classes {:?}; non-joined pairs by reason {:?}; {} of the full check's {} conditions answered from the memo; {} definitions with a pair the load's scope skipped; {} axiom instances judged in D+ ({} over constants; {} terms free of constants compared with the definition; {} definitions with witness equations, {} instances of them); {} failures",
            self.definitions,
            self.rejected,
            self.accepted,
            self.partially_tainted,
            self.outside_totality,
            self.queries,
            self.nonterminating,
            self.classes,
            self.reasons,
            self.memo_hits,
            self.memo_conditions,
            self.with_skipped_pair,
            self.junk_instances,
            self.junk_constant_instances,
            self.junk_agreements,
            self.junk_witnessed,
            self.junk_witness_instances,
            self.failures.len()
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
    if !definition.hooked_heads.is_empty() {
        classes.insert(Class::HookedHead);
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
    match sort.node() {
        SortNode::Application { name, arguments } if arguments.is_empty() => {
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

/// The claims the backend makes about one ground term.
struct Claims {
    token: bool,
    /// `\ceil` simplified to `\top`.
    ceil_top: bool,
}

fn claims(backend: &BackendDefinition, kore: &str, sort: &str) -> Result<Claims, String> {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let _deadline = deadline();
        let term = backend
            .internalize_term(&parse_pattern(kore).expect("the term parses"), &[])
            .map_err(|error| format!("{kore} does not internalize: {error:?}"))?;
        let token = backend.instance_normal(&term).is_some();
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
        let ceil_top = match simplified {
            Ok(Ok(Predicate::True)) => true,
            Ok(_) => false,
            // A stop (the deadline, the stack guard) claims nothing.
            Err(stop) => {
                stop.into_cause();
                false
            }
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

/// Checks `definition` against the backend's own verdicts: V9 (the load's scope and the full
/// check admit the same claims and warn about the same pairs) and the memo (the full check with
/// and without its memo of condition simplifications reaches the same verdict and the same
/// counts but the memo's own work). The verdict's acceptance and taint set are the full check's.
pub(super) fn check_definition(label: &str, definition: &Definition) -> (Tally, Verdict) {
    let mut tally = Tally {
        definitions: 1,
        ..Tally::default()
    };
    for class in classes(definition) {
        tally.classes.insert(class, 1);
    }
    let mut verdict = Verdict::default();
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
    // warn about the same pairs.
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
    // The sorts with an element in every model, recomputed in the oracle's language, are the
    // backend's; and where the full check reports nothing, `D+` is a model of the axioms.
    for failure in inhabitation_failures(definition, &backend) {
        tally
            .failures
            .push(format!("{label}: {JUNK}: {failure}\n{}", describe()));
    }
    // The verdict's witness equations, read in the oracle's language: well formed, and none
    // headed by a symbol the full check's closure taints.
    let witnesses = match witness_equations(definition, &full) {
        Ok(witnesses) => witnesses,
        Err(error) => {
            tally
                .failures
                .push(format!("{label}: {WITNESS}: {error}\n{}", describe()));
            Vec::new()
        }
    };
    for failure in witness_failures(definition, &witnesses, &full) {
        tally
            .failures
            .push(format!("{label}: {WITNESS}: {failure}\n{}", describe()));
    }
    if full.unjoined().is_empty() && full.violations().is_empty() && !definition.collections {
        let run = junk_check(definition, &witnesses, true, &mut Rng(JUNK_SEED));
        tally.junk_instances += run.instances;
        tally.junk_constant_instances += run.with_constants;
        tally.junk_agreements += run.agreements;
        tally.junk_witnessed += usize::from(!witnesses.is_empty());
        tally.junk_witness_instances += run.witness_instances;
        for failure in run.failures {
            tally.failures.push(format!(
                "{label}: {JUNK}: the full check reports nothing, but {failure}\n{}",
                describe()
            ));
        }
    }
    let has_head = definition.symbols.iter().any(|symbol| symbol.is_head());
    // Without an equation head the check stops after the precondition rows: it accepts nothing.
    verdict.accepted = has_head && full.unjoined().is_empty() && full.violations().is_empty();
    verdict.tainted = full
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
    for pair in full.unjoined() {
        let reason = match &pair.reason {
            crate::confluence::UnjoinedReason::Unresolved(shape) => format!("unresolved {shape}"),
            reason => format!("{reason:?}"),
        };
        *tally.reasons.entry(reason).or_default() += 1;
    }
    (tally, verdict)
}

/// The tag of the constants check's failures: the oracle's surely-inhabited sorts differ from
/// the backend's, or `D+` (the definition with a free constant in each sort outside them, the
/// design's `M+`, P7-EMPTYJOIN 4.1 and 4.3) is no model of the axioms of a definition the full
/// check accepts.
pub(super) const JUNK: &str = "M+";

/// The tag of the witness equations' failures: a witness of the verdict
/// (`ValueClaims::witnesses`) the oracle's language cannot read, that is not well formed (the
/// design's 4.1, read in the oracle's language), or whose head the full check's closure taints
/// (adoption condition 4: the claims' model `M'` interprets a tainted symbol by any model, which
/// need not satisfy the witness).
pub(super) const WITNESS: &str = "W";

/// The priority of the witness equations in `D+`: below every priority group a definition of
/// the oracle's language writes.
pub(super) const WITNESS_PRIORITY: u8 = u8::MAX;

/// The oracle's pattern of a backend pattern, when it is one the oracle's language writes over
/// `definition`'s symbols and sorts.
fn oracle_pattern(definition: &Definition, term: &Term) -> Option<Pat> {
    let sort = |sort: &Sort| {
        let name = sort_name(sort)?;
        definition.all_sorts().contains(&name).then_some(name)
    };
    match term.kind() {
        TermKind::Variable(variable) => {
            Some(Pat::Var(variable.name.to_string(), sort(&variable.sort)?))
        }
        TermKind::Application {
            symbol, arguments, ..
        } => {
            let name = symbol.name.to_string();
            if !definition.symbols.iter().any(|symbol| symbol.name == name) {
                return None;
            }
            let arguments = arguments
                .iter()
                .map(|argument| oracle_pattern(definition, argument))
                .collect::<Option<Vec<_>>>()?;
            Some(Pat::App(name, arguments))
        }
        TermKind::Injection {
            source,
            target,
            term,
        } => Some(Pat::Inj(
            sort(source)?,
            sort(target)?,
            Box::new(oracle_pattern(definition, term)?),
        )),
        TermKind::DomainValue { sort: of, value } if sort_name(of).as_deref() == Some("Int") => {
            Some(Pat::Int(
                std::str::from_utf8(value.as_bytes()).ok()?.parse().ok()?,
            ))
        }
        _ => None,
    }
}

/// The witness equations of `claims` (`ValueClaims::witnesses`) as equations of the oracle's
/// language at [`WITNESS_PRIORITY`], below every group of their head; an error names a witness
/// the language does not write (a witness has no condition and a term right-hand side).
pub(super) fn witness_equations(
    definition: &Definition,
    claims: &crate::confluence::ValueClaims,
) -> Result<Vec<Equation>, String> {
    claims
        .witnesses()
        .iter()
        .map(|rule| {
            let unreadable = || {
                format!(
                    "the witness {} is not an equation of the oracle's language",
                    rule.attributes.unique_id
                )
            };
            let crate::rule::RuleRhs::Term(rhs) = &rule.rhs else {
                return Err(unreadable());
            };
            if !(rule.requires.is_empty() && rule.ensures.is_empty()) {
                return Err(unreadable());
            }
            let (Some(lhs @ Pat::App(..)), Some(rhs)) = (
                oracle_pattern(definition, &rule.lhs),
                oracle_pattern(definition, rhs),
            ) else {
                return Err(unreadable());
            };
            Ok(Equation {
                lhs,
                rhs,
                requires: None,
                ensures: None,
                priority: WITNESS_PRIORITY,
                overload: None,
                symbolic: false,
            })
        })
        .collect()
}

/// Where the `witnesses` of the full check's verdict `full`, read in the oracle's language, fail
/// the design's well-formedness (P7-EMPTYJOIN 4.1) or adoption condition 4. A witness `p => t`
/// must apply a partial function (declared `function`, not `total`) that is not overloaded to
/// constructor, injection and variable terms, and hold a variable of a sort outside the
/// oracle's surely-inhabited ones (a sort with no normal form is one: a surely-inhabited sort has
/// a ground term, which evaluates to a defined element under P2); `t` must be built from
/// constructors, injections and `p`'s variables, at a sort below `p`'s; and no definition
/// equation may sit at the witnesses' priority. Its head must not be a symbol the full check's
/// closure taints: the claims' model interprets a tainted symbol by an arbitrary model, which
/// need not satisfy the witness, so a join step through it would hold in no model the claims
/// name.
pub(super) fn witness_failures(
    definition: &Definition,
    witnesses: &[Equation],
    full: &crate::confluence::ValueClaims,
) -> Vec<String> {
    fn built(
        definition: &Definition,
        pattern: &Pat,
        variables: Option<&BTreeMap<String, String>>,
    ) -> bool {
        match pattern {
            Pat::Var(name, _) => variables.is_none_or(|variables| variables.contains_key(name)),
            Pat::Inj(_, _, inner) => built(definition, inner, variables),
            Pat::App(name, arguments) => {
                definition.symbol_named(name).kind == Kind::Constructor
                    && arguments
                        .iter()
                        .all(|argument| built(definition, argument, variables))
            }
            Pat::Int(_) | Pat::As(..) | Pat::List(..) => false,
        }
    }
    let sort_of = |pattern: &Pat| match pattern {
        Pat::Var(_, sort) | Pat::Inj(_, sort, _) => Some(sort.clone()),
        Pat::App(name, _) => Some(definition.symbol_named(name).result.clone()),
        _ => None,
    };
    let junk = definition.junk_sorts();
    let order = definition.sort_order();
    let overloaded = definition
        .overloads()
        .into_iter()
        .flat_map(|(greater, lesser)| [greater, lesser])
        .collect::<BTreeSet<_>>();
    let tainted = full
        .tainted_symbols()
        .iter()
        .map(ToString::to_string)
        .collect::<BTreeSet<_>>();
    let mut failures = Vec::new();
    if !witnesses.is_empty()
        && definition
            .equations
            .iter()
            .any(|equation| equation.priority == WITNESS_PRIORITY)
    {
        failures.push("a definition equation sits at the witnesses' priority".to_owned());
    }
    for witness in witnesses {
        let text = format!("{} => {}", show(&witness.lhs), show(&witness.rhs));
        let Pat::App(head, arguments) = &witness.lhs else {
            unreachable!("witness_equations reads applications only");
        };
        let mut variables = BTreeMap::new();
        pattern_variables(&witness.lhs, &mut variables);
        let symbol = definition.symbol_named(head);
        let problems = [
            (
                symbol.kind == (Kind::Function { total: false }) && !overloaded.contains(head),
                "its head is no partial function that is not overloaded",
            ),
            (
                arguments
                    .iter()
                    .all(|argument| built(definition, argument, None)),
                "an argument of its left-hand side is not built from constructors, injections and variables",
            ),
            (
                variables.values().any(|sort| junk.contains(sort)),
                "its left-hand side holds no variable of a sort outside the surely-inhabited ones",
            ),
            (
                built(definition, &witness.rhs, Some(&variables)),
                "its right-hand side is not built from constructors, injections and the left-hand side's variables",
            ),
            (
                sort_of(&witness.rhs).is_some_and(|sort| order[&symbol.result].contains(&sort)),
                "its right-hand side's sort is not below its head's",
            ),
            (
                !tainted.contains(head),
                "its head is tainted in the full check's closure (adoption condition 4)",
            ),
        ];
        for (holds, problem) in problems {
            if !holds {
                failures.push(format!("the witness {text}: {problem}"));
            }
        }
    }
    failures
}

/// The seed of the constants check's valuations.
const JUNK_SEED: u64 = 0x5eed_0a11;

/// Valuations per equation in the constants check: all of them up to this many, otherwise this
/// many drawn, and one more that takes a value holding a constant wherever one exists.
const JUNK_VALUATIONS: usize = 12;

/// Where the sorts with an element in every model, computed in the oracle's own language
/// ([`Definition::surely_inhabited`]), differ from the backend's (`Sorts::surely_inhabited`),
/// over every sort of the definition. The set's complement `J` is the one set the model `M+`
/// adds constants to, which the coverage condition of part F and the oracle's `D+` read too, so
/// the backend's reading of it is tested, not assumed.
pub(super) fn inhabitation_failures(
    definition: &Definition,
    backend: &BackendDefinition,
) -> Vec<String> {
    let sorts = crate::confluence::symbols::Sorts::of(backend);
    let oracle = definition.surely_inhabited();
    definition
        .all_sorts()
        .into_iter()
        .filter_map(|sort| {
            let theirs = sorts.surely_inhabited(&Sort::simple(format!("Sort{sort}")));
            let ours = oracle.contains(&sort);
            (theirs != ours).then(|| {
                format!(
                    "the oracle reads `{sort}` as {}surely inhabited, the backend as {}",
                    if ours { "" } else { "not " },
                    if theirs { "surely inhabited" } else { "not" }
                )
            })
        })
        .collect()
}

/// What the constants check of one definition counted and found.
#[derive(Debug, Default)]
pub(super) struct JunkRun {
    /// Axiom instances judged: each side has one normal form, and the instance's premise holds.
    pub(super) instances: usize,
    /// Of those, the instances whose valuation holds a constant.
    pub(super) with_constants: usize,
    /// Terms free of constants whose normal forms in `D+` were compared with the definition's.
    pub(super) agreements: usize,
    /// Of `instances`, those of witness equations.
    pub(super) witness_instances: usize,
    pub(super) failures: Vec<String>,
}

/// The constants check (FZ-JUNK-ORACLE, FZ-EMPTYJOIN-ORACLE; P7-EMPTYJOIN 4.3) of a definition
/// whose full check reports nothing, with the oracle's own evaluator.
///
/// When every overlap of the definition's equations `R` and the verdict's witness equations
/// `witnesses` (`W`, already in the oracle's language, [`witness_equations`]) is refuted or
/// joined by steps valid on every instance, the normal forms of innermost evaluation by `R ∪ W`
/// over the signature extended with a fresh free constant `*_S` in each sort `S` outside the
/// surely-inhabited ones (`D+`, the design's `M+`) are a model of the axioms of `R ∪ W`: every
/// model of a definition has an element of every sort, and the constant stands for one that no
/// term of the signature denotes. Each witness is an equation of the lowest priority group of
/// its head. So in `D+`, at each instance of an executable equation `l = r` of `R ∪ W` by values
/// (normal forms other than `\bottom`, constants included), each side has one normal form; where
/// the premise holds (the `requires` evaluates to `true`, and no equation of a higher priority
/// group applies at `l`'s root once its arguments are evaluated) the two are the same, `\bottom`
/// standing for the right-hand side where the `ensures` evaluates to `false`. A term free of
/// constants evaluates in `D+` as in the definition without `W`: a witness applies only to a
/// term that holds a constant. Without `constants` the same check runs on the definition itself,
/// whose sorts without a normal form then have no value: an overlap over such a sort has no
/// instance there.
///
/// An instance whose evaluation does not end within the oracle's bounds (outside P0), or that
/// meets a hook on a term other than a literal, is skipped.
pub(super) fn junk_check(
    definition: &Definition,
    witnesses: &[Equation],
    constants: bool,
    rng: &mut Rng,
) -> JunkRun {
    let sorts = if constants {
        definition.junk_sorts()
    } else {
        BTreeSet::new()
    };
    let mut plus = definition.with_junk_constants(&sorts);
    plus.equations.extend(witnesses.iter().cloned());
    let mut universe = Universe::new(&plus);
    let mut plain = Universe::new(definition);
    let mut values = values(&mut universe, rng);
    // Every constant is a value of its sort, whatever the cap on the values of a sort left.
    for sort in &sorts {
        let constant = universe.ground(&Pat::App(junk_constant(sort), Vec::new()));
        let entry = values.entry(universe.sort_id(sort)).or_default();
        if !entry.contains(&constant) {
            entry.insert(0, constant);
        }
    }
    let mut run = JunkRun::default();
    for equation in &plus.equations {
        if equation.symbolic {
            continue;
        }
        // The variables outside aliases are drawn; an alias `\and(p, X)` binds `X` to `p`'s
        // instance, innermost first, and where `X` also occurs outside aliases the valuation is
        // an instance only when the two agree.
        let mut variables = BTreeMap::new();
        pattern_variables(&without_aliases(&equation.lhs), &mut variables);
        let mut aliases = Vec::new();
        alias_patterns(&equation.lhs, &mut aliases);
        let mut sampled = Vec::new();
        for (name, sort) in &variables {
            let sort = universe.sort_id(sort);
            sampled.push((name.clone(), candidates_of(&mut universe, &values, sort)));
        }
        if sampled.iter().any(|(_, candidates)| candidates.is_empty()) {
            continue;
        }
        'valuations: for mut valuation in junk_valuations(&universe, &sampled, rng) {
            for (alias, pattern) in &aliases {
                let instance = universe.instantiate(pattern, &valuation);
                if *valuation.entry(alias.clone()).or_insert(instance) != instance {
                    continue 'valuations;
                }
            }
            let before = run.instances;
            judge_instance(&mut universe, &mut plain, equation, &valuation, &mut run);
            if equation.priority == WITNESS_PRIORITY {
                run.witness_instances += run.instances - before;
            }
        }
    }
    run
}

/// The aliases `\and(p, X)` of `pattern`, innermost first, each with `p` without aliases.
fn alias_patterns(pattern: &Pat, into: &mut Vec<(String, Pat)>) {
    match pattern {
        Pat::As(inner, name, _) => {
            alias_patterns(inner, into);
            into.push((name.clone(), without_aliases(inner)));
        }
        Pat::App(_, arguments) => {
            for argument in arguments {
                alias_patterns(argument, into);
            }
        }
        Pat::Inj(_, _, inner) => alias_patterns(inner, into),
        Pat::List(prefix, _, suffix) => {
            for element in prefix.iter().chain(suffix) {
                alias_patterns(element, into);
            }
        }
        Pat::Var(..) | Pat::Int(_) => {}
    }
}

/// Whether `id` holds one of `D+`'s constants.
fn holds_junk(universe: &Universe<'_>, id: Id) -> bool {
    universe.holds_symbol(id, &|name: &str| name.starts_with(JUNK_PREFIX))
}

/// The valuations of `sampled` (each variable with its candidate values) the constants check
/// judges: all of them when there are at most [`JUNK_VALUATIONS`], otherwise that many drawn;
/// and the valuation that gives each variable its first candidate holding a constant, where it
/// has one.
fn junk_valuations(
    universe: &Universe<'_>,
    sampled: &[(String, Vec<Id>)],
    rng: &mut Rng,
) -> Vec<HashMap<String, Id>> {
    let total = sampled
        .iter()
        .try_fold(1usize, |product, (_, candidates)| {
            product.checked_mul(candidates.len())
        })
        .unwrap_or(usize::MAX);
    let mut valuations = Vec::new();
    if total <= JUNK_VALUATIONS {
        let mut all = vec![HashMap::new()];
        for (name, candidates) in sampled {
            all = all
                .into_iter()
                .flat_map(|valuation: HashMap<String, Id>| {
                    candidates.iter().map(move |candidate| {
                        let mut extended = valuation.clone();
                        extended.insert(name.clone(), *candidate);
                        extended
                    })
                })
                .collect();
        }
        valuations = all;
    } else {
        for _ in 0..JUNK_VALUATIONS {
            valuations.push(
                sampled
                    .iter()
                    .map(|(name, candidates)| (name.clone(), *rng.pick(candidates)))
                    .collect(),
            );
        }
        let with_junk = sampled
            .iter()
            .map(|(name, candidates)| {
                let chosen = candidates
                    .iter()
                    .find(|candidate| holds_junk(universe, **candidate))
                    .unwrap_or(&candidates[0]);
                (name.clone(), *chosen)
            })
            .collect::<HashMap<_, _>>();
        if !valuations.contains(&with_junk) {
            valuations.push(with_junk);
        }
    }
    valuations
}

/// The one normal form of `id` in `universe`: `None` when its evaluation does not end within the
/// bounds, and also when it has several, which is recorded in `run` as a failure.
fn one_normal_form(
    universe: &mut Universe<'_>,
    id: Id,
    what: &str,
    run: &mut JunkRun,
) -> Option<Id> {
    let normal = universe.normalize(id);
    if !normal.complete {
        return None;
    }
    if normal.forms.len() != 1 {
        run.failures.push(format!(
            "{what} {} has the normal forms {}",
            universe.show(id),
            normal
                .forms
                .iter()
                .map(|form| universe.show(*form))
                .collect::<Vec<_>>()
                .join(", ")
        ));
        return None;
    }
    Some(normal.forms[0])
}

/// Whether the term `id` of `D+` free of constants evaluates in the definition (`plain`) to
/// the same normal forms, when both evaluations end; a difference is recorded in `run`.
fn agrees_with_the_definition(
    universe: &mut Universe<'_>,
    plain: &mut Universe<'_>,
    id: Id,
    run: &mut JunkRun,
) {
    if id == BOTTOM || holds_junk(universe, id) {
        return;
    }
    let moved = universe.transfer(id, plain);
    let (here, there) = (universe.normalize(id), plain.normalize(moved));
    if !(here.complete && there.complete) {
        return;
    }
    run.agreements += 1;
    let mut forms = here
        .forms
        .iter()
        .map(|form| universe.transfer(*form, plain))
        .collect::<Vec<_>>();
    forms.sort_unstable();
    if forms != there.forms {
        run.failures.push(format!(
            "{} evaluates in D+ to {:?} and in the definition to {:?}",
            universe.show(id),
            here.forms
                .iter()
                .map(|form| universe.show(*form))
                .collect::<Vec<_>>(),
            there
                .forms
                .iter()
                .map(|form| plain.show(*form))
                .collect::<Vec<_>>()
        ));
    }
}

/// Judges the instance of `equation` by `valuation` in `D+` ([`junk_check`]).
fn judge_instance(
    universe: &mut Universe<'_>,
    plain: &mut Universe<'_>,
    equation: &Equation,
    valuation: &HashMap<String, Id>,
    run: &mut JunkRun,
) {
    let left = universe.instantiate(&without_aliases(&equation.lhs), valuation);
    let right = universe.instantiate(&equation.rhs, valuation);
    for side in [left, right] {
        agrees_with_the_definition(universe, plain, side, run);
    }
    let over = if valuation.values().any(|value| holds_junk(universe, *value)) {
        " over constants"
    } else {
        ""
    };
    let Some(left_form) =
        one_normal_form(universe, left, &format!("the left-hand side{over}"), run)
    else {
        return;
    };
    let Some(right_form) =
        one_normal_form(universe, right, &format!("the right-hand side{over}"), run)
    else {
        return;
    };
    // The premise: the root's arguments evaluate to elements, the `requires` to `true`, and no
    // equation of a higher priority group applies at the root on those elements.
    let Node::App(symbol, arguments) = universe.node_of(left).clone() else {
        return;
    };
    let mut elements = Vec::new();
    for argument in arguments {
        match one_normal_form(universe, argument, "the argument", run) {
            Some(element) if element != BOTTOM => elements.push(element),
            _ => return,
        }
    }
    let root = universe.node(Node::App(symbol, elements));
    let truth = universe.boolean(true);
    if let Some(requires) = &equation.requires {
        let condition = universe.instantiate(requires, valuation);
        if one_normal_form(universe, condition, "the requires", run) != Some(truth) {
            return;
        }
    }
    let (applying, complete) = universe.applicable(root);
    let definition = universe.definition;
    if !complete
        || applying
            .iter()
            .any(|(index, _)| definition.equations[*index].priority < equation.priority)
    {
        return;
    }
    let expected = match &equation.ensures {
        None => right_form,
        Some(ensures) => {
            let condition = universe.instantiate(ensures, valuation);
            match one_normal_form(universe, condition, "the ensures", run) {
                None => return,
                Some(holds) if holds == truth => right_form,
                Some(_) => BOTTOM,
            }
        }
    };
    run.instances += 1;
    if !over.is_empty() {
        run.with_constants += 1;
    }
    if left_form != expected {
        run.failures.push(format!(
            "the instance {} = {}{over} does not hold in D+: the left-hand side evaluates to {}, the right-hand side to {}",
            universe.show(left),
            universe.show(right),
            universe.show(left_form),
            universe.show(expected)
        ));
    }
}

/// Asks the loaded `definition` about the probe terms `probes`: for each whose evaluation under
/// `->E` ends, in order, whether it keeps its `\ceil` obligation and whether it gets a token. A
/// probe's expectation is stated inside the preconditions P0 and P2, or about the violation of
/// one, so the oracle's evaluator also explores the ground terms around the probes and the
/// instances of the equations (seeded with `seeds`), and counts the queries whose evaluation
/// does not end (outside P0) and whether a total symbol is reached undefined on defined
/// arguments (outside P2). A definition the backend rejects is asked nothing
/// ([`check_definition`] reports it).
pub(super) fn ask_probes(
    label: &str,
    definition: &Definition,
    seeds: &[Pat],
    probes: &[Pat],
    rng: &mut Rng,
) -> (Tally, Vec<(bool, bool)>) {
    let mut tally = Tally::default();
    let Ok(backend) = backend(definition) else {
        return (tally, Vec::new());
    };
    let verbose = std::env::var_os("KRUST_DEFINEDNESS_ORACLE_VERBOSE").is_some();
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
    for id in asked.clone() {
        let mut subterms = vec![id];
        while let Some(term) = subterms.pop() {
            if universe.violates_totality(term) {
                tally.outside_totality = 1;
            }
            subterms.extend(universe.children(term));
        }
    }
    let mut answers = HashMap::new();
    for id in asked {
        tally.queries += 1;
        let normal = universe.normalize(id);
        if verbose {
            eprintln!(
                "{label}: {} -> {:?}",
                universe.show(id),
                normal
                    .forms
                    .iter()
                    .map(|form| universe.show(*form))
                    .collect::<Vec<_>>()
            );
        }
        if !normal.complete {
            tally.nonterminating += 1;
            continue;
        }
        if !probe_ids.contains(&id) {
            continue;
        }
        let sort = universe.sort_name(universe.sort_of(id)).to_owned();
        match claims(&backend, &universe.kore(id), &sort) {
            Ok(found) => {
                answers.insert(id, (!found.ceil_top, found.token));
            }
            Err(failure) => tally.failures.push(format!(
                "{label}: {failure}\n  definition:\n{}",
                describe(definition)
            )),
        }
    }
    let answers = probe_ids
        .iter()
        .filter_map(|id| answers.get(id).copied())
        .collect();
    (tally, answers)
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

/// The oracle's surely-inhabited sorts on one sort per kind of producer, with and without the
/// collection sorts, and the backend's agree: a sort is surely inhabited through a literal or a
/// collection unit, a constructor, a symbol declared total (a function, an equation head, a
/// `functional` symbol) on surely-inhabited arguments, or a subsort; not through an equation
/// head or a function that is not declared total, nor through a constructor of an argument sort
/// that is not surely inhabited. Those sorts are `J`, and `D+` gives each a constant.
#[test]
fn the_oracles_surely_inhabited_sorts_are_the_backends() {
    super::on_large_stack(|| {
        for collections in [false, true] {
            let mut definition = Definition::new(&["A"])
                .with_lists()
                .constructor("c", &[], "A")
                .head("hHd", &["Int"], "Hd")
                .total_function("tTf", &["Int"], "Tf")
                .function("pPf", &["Int"], "Pf")
                .total_head("tTh", &["Int"], "Th")
                .functional("uFn", &["A"], "Fn")
                .constructor("cCh", &["Em"], "Ch")
                .constructor("cTe", &["Em"], "Te")
                .total_function("tTe", &["Hd"], "Te")
                .subsort("A", "Sup")
                .subsort("Lo", "Hd");
            if collections {
                definition = definition.with_collections();
            }
            for sort in ["Em", "Hd", "Tf", "Pf", "Th", "Fn", "Ch", "Te", "Sup", "Lo"] {
                definition.sorts.push(sort.into());
            }
            let mut expected = vec!["A", "Bool", "Fn", "Int", "List", "S", "Sup", "Tf", "Th"];
            if collections {
                expected.extend(["Map", "Mv", "Set"]);
            }
            expected.sort_unstable();
            assert_eq!(
                definition.surely_inhabited(),
                expected.iter().map(|sort| (*sort).to_owned()).collect(),
                "collections {collections}"
            );
            assert_eq!(
                definition.junk_sorts(),
                ["Ch", "Em", "Hd", "Lo", "Pf", "Te"]
                    .iter()
                    .map(|sort| (*sort).to_owned())
                    .collect(),
                "collections {collections}"
            );
            let loaded = backend(&definition).expect("the definition loads");
            let failures = inhabitation_failures(&definition, &loaded);
            assert!(failures.is_empty(), "{}", failures.join("\n"));
        }
    });
}
