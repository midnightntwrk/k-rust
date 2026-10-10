//! The axiom-instance harness: the value claims checked against the axioms they rest on, with
//! the backend's own evaluation as the judge and no second engine.
//!
//! A value claim says that the evaluator's normal forms, at the indexes the load-time check
//! leaves untainted, are elements of a model of the definition: a certified normal form is a
//! defined element, and two different claimed values are different elements. Every executable
//! equation is an axiom of every model, so each of its instances by defined elements holds in
//! that model. The harness instantiates every executable equation `l = r` with the elements the
//! backend says are defined (built bottom-up from the definition's symbols and evaluated by the
//! backend: the values it claims, and the normal forms whose `\ceil` it discharges), and judges
//! with the backend:
//!
//! - **Axiom instances.** At an instance `σ` where the `requires` holds and no equation of a
//!   higher priority group applies (both decided by the backend's own simplifier and matcher),
//!   `lσ` and `rσ` must not evaluate to two different claimed values, nor one to a claimed
//!   value (or to a term whose `\ceil` the backend discharges through an equation head) and the
//!   other to `\bottom`. For an equation rooted at a hooked symbol the left value is the hook's
//!   result on the instance where the hook applies, which is what the symbol denotes there (where
//!   it does not, the equations alone give the value, and the backend's evaluation is the judge).
//!   For an equation whose left-hand side the collection laws normalize to a collection pattern
//!   or a bare variable, the instance is a collection of values and denotes itself, and the right
//!   value is the collection of the right-hand side's separately evaluated parts, so that neither
//!   side is the equation's own result. A contradiction whose valuation
//!   and values hold no application of a symbol the claims are about (an equation head, or an
//!   overloaded symbol that is not a free constructor; against `\bottom`, one declared total
//!   counts as the declaration's) rests on no claim: it shows that the definition has no model.
//!   Then the full check must name a pair, since a definition whose every pair joins has the
//!   model of its normal forms, and the definition gets no further guarantee, so nothing else of
//!   it is judged. Every other contradiction is a claim that holds in no model.
//! - **Withheld claims.** A claim is an extra true fact: a ground result the evaluator decides
//!   with every claim withheld (a claimed value or `\bottom`) is not contradicted by the result
//!   it decides with them (which may stay undecided).
//! - **Equation order.** A definition the full check accepts gives every ground term one normal
//!   form, so its ground terms evaluate alike with its axioms written in the reverse order.
//! - **Decisions about terms with variables.** A token, a `\ceil` discharge or a simplification
//!   of an instance with one of its first two arguments replaced by a variable holds for every
//!   value of the variable, so it holds at each value the harness has.
//!
//! An instance whose `requires`, `ensures`, priority or sides the backend leaves undecided is
//! skipped and counted. The contract states and does not check that evaluation ends (P0), that
//! a symbol declared total is defined on defined arguments (P2), and that a `symbolic` equation
//! is a theorem of the executable ones: a definition where a backend call stops or an evaluation
//! contradicts a `total` declaration gets no guarantee and is counted, not judged, and the
//! instances of a `symbolic` equation, which never applies to a ground term, are not judged.

use std::{
    collections::{BTreeMap, BTreeSet},
    panic::{AssertUnwindSafe, catch_unwind},
    sync::Arc,
};

use k_rust_kore::kore::parser::parse_pattern;

use super::{
    Rng,
    checks::{backend, deadline},
    language::Definition,
};
use crate::{
    builtin::{BuiltinResult, evaluate_in_definition},
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::{Concreteness, ConstraintKind, Predicate, RewriteRule, RuleRhs},
    simplify::{Simplification, SimplificationOptions, simplify, simplify_predicate_with_solver},
    smt::NoSolver,
    substitution::{Substitution, substitute},
    term::{FunctionType, HeadRole, Sort, SymbolType, Term, TermKind, Variable},
};

/// Values kept per sort.
const VALUES_PER_SORT: usize = 6;

/// Valuations per equation: all of them up to this many, otherwise this many drawn.
const VALUATIONS: usize = 8;

/// Values each generalization is instantiated with.
const GENERALIZED_VALUES: usize = 4;

/// What the harness counted and found over one or more definitions.
#[derive(Debug, Default)]
pub(super) struct AxiomTally {
    pub(super) definitions: usize,
    /// Rejected by parsing or internalization.
    pub(super) rejected: usize,
    /// Executable equations whose instances were drawn.
    pub(super) equations: usize,
    /// Instances where the `requires` held and no higher group applied.
    pub(super) instances: usize,
    /// Instances skipped because the backend left their `requires`, `ensures`, priority or a
    /// side undecided.
    pub(super) undecided: usize,
    /// Instances whose two sides were both decided (a claimed value or `\bottom`), the ones that
    /// can contradict.
    pub(super) compared: usize,
    /// Of those, instances judged against a hook's value: at a hooked root where the hook
    /// applies, or at a collection the collection laws give.
    pub(super) hooked: usize,
    /// Definitions a contradiction resting on no claim shows to have no model.
    pub(super) without_model: usize,
    /// Definitions where an evaluation found a `total` symbol undefined on defined arguments.
    pub(super) outside_totality: usize,
    /// Definitions where an evaluation did not end within the bounds.
    pub(super) outside_termination: usize,
    /// Results decided with every claim withheld, compared with the loaded definition's.
    pub(super) withheld_decided: usize,
    /// Ground terms of accepted definitions evaluated in two orders of their axioms.
    pub(super) reordered: usize,
    /// Generalizations with a decision checked at some value.
    pub(super) generalizations: usize,
    pub(super) failures: Vec<String>,
}

impl AxiomTally {
    pub(super) fn add(&mut self, other: Self) {
        self.definitions += other.definitions;
        self.rejected += other.rejected;
        self.equations += other.equations;
        self.instances += other.instances;
        self.undecided += other.undecided;
        self.compared += other.compared;
        self.hooked += other.hooked;
        self.without_model += other.without_model;
        self.outside_totality += other.outside_totality;
        self.outside_termination += other.outside_termination;
        self.withheld_decided += other.withheld_decided;
        self.reordered += other.reordered;
        self.generalizations += other.generalizations;
        self.failures.extend(other.failures);
    }

    pub(super) fn summary(&self, name: &str) -> String {
        format!(
            "{name}: {} definitions ({} rejected, {} shown to have no model, {} outside P2, {} outside P0), {} equations, {} instances ({} undecided, {} compared, {} at a hooked root), {} results decided without claims, {} terms evaluated in two axiom orders, {} generalizations; {} failures",
            self.definitions,
            self.rejected,
            self.without_model,
            self.outside_totality,
            self.outside_termination,
            self.equations,
            self.instances,
            self.undecided,
            self.compared,
            self.hooked,
            self.withheld_decided,
            self.reordered,
            self.generalizations,
            self.failures.len()
        )
    }
}

/// What the backend decides a ground term is.
#[derive(Clone, Debug)]
enum Outcome {
    /// A value it claims.
    Value(Term),
    /// `\bottom`.
    Bottom,
    /// Neither: a stuck or constrained result, or no result.
    Open,
}

impl Outcome {
    fn decided(&self) -> bool {
        !matches!(self, Self::Open)
    }

    fn show(&self) -> String {
        match self {
            Self::Value(term) => show(term),
            Self::Bottom => r"\bottom".into(),
            Self::Open => "undecided".into(),
        }
    }
}

/// Whether two decided outcomes contradict: two different values, or a value and `\bottom`.
fn contradict(left: &Outcome, right: &Outcome) -> bool {
    match (left, right) {
        (Outcome::Value(left), Outcome::Value(right)) => left != right,
        (Outcome::Value(_), Outcome::Bottom) | (Outcome::Bottom, Outcome::Value(_)) => true,
        _ => false,
    }
}

pub(super) fn show(term: &Term) -> String {
    k_rust_kore::kore::printer::Printer::compact().print_pattern(&crate::externalize::term(term))
}

/// A term the backend claims as a value: an application, injection or literal it marks as one,
/// or a collection without a rest whose entries are claimed values. A map that binds a key twice
/// or a set that holds an element twice is `\bottom` (`Term::map`, `Term::set`), not a value.
fn claimed_value(term: &Term) -> bool {
    if term.repeated_collection_key().is_some() {
        return false;
    }
    match term.kind() {
        TermKind::List { heads, rest, .. } => rest.is_none() && heads.iter().all(claimed_value),
        TermKind::Set { elements, rest, .. } => {
            rest.is_none() && elements.iter().all(claimed_value)
        }
        TermKind::Map { entries, rest, .. } => {
            rest.is_none()
                && entries
                    .iter()
                    .all(|(key, value)| claimed_value(key) && claimed_value(value))
        }
        TermKind::Variable(_) | TermKind::And(..) => false,
        TermKind::Application { .. }
        | TermKind::Injection { .. }
        | TermKind::DomainValue { .. } => term.attributes().value_claimed(),
    }
}

/// Whether the backend's claims are about the applications of `symbol`: an equation head, or
/// an overloaded symbol that is neither a free constructor nor hooked (the symbols a pair can
/// withdraw).
fn claimable(backend: &BackendDefinition, symbol: &crate::term::Symbol) -> bool {
    let role = symbol.attributes.head_role();
    role == HeadRole::EquationHead
        || (crate::confluence::certified_root(backend, symbol)
            && role != HeadRole::FreeConstructor
            && symbol.attributes.hook.is_none())
}

/// Whether `term` holds no application of a [`claimable`] symbol: its value and definedness are
/// fixed by the definition's own axioms (literals, constructors, injections, collections, and
/// symbols declared total), and stating them makes no claim. With `definedness_only`, an
/// application of a claimable symbol declared total counts too: its definedness is the
/// declaration's (an author axiom), although its value is a claim.
fn claim_free(backend: &BackendDefinition, term: &Term, definedness_only: bool) -> bool {
    let free = |term: &Term| claim_free(backend, term, definedness_only);
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            let total = matches!(
                symbol.attributes.symbol_type,
                SymbolType::Function(FunctionType::Total)
            );
            (!claimable(backend, symbol) || (definedness_only && total))
                && arguments.iter().all(free)
        }
        TermKind::Injection { term, .. } => free(term),
        TermKind::List { heads, rest, .. } => {
            heads.iter().all(free)
                && rest
                    .as_ref()
                    .is_none_or(|(middle, tail)| free(middle) && tail.iter().all(free))
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().all(free) && rest.as_ref().is_none_or(free)
        }
        TermKind::Map { entries, rest, .. } => {
            entries.iter().all(|(key, value)| free(key) && free(value))
                && rest.as_ref().is_none_or(free)
        }
        TermKind::DomainValue { .. } => true,
        TermKind::Variable(_) | TermKind::And(..) => false,
    }
}

/// Whether `term` holds an application of an equation head: a `\ceil` discharge of it is a
/// claim (a value production's), not the definition's own `functional` or `total` axiom.
fn holds_equation_head(term: &Term) -> bool {
    match term.kind() {
        TermKind::Application {
            symbol, arguments, ..
        } => {
            symbol.attributes.head_role() == HeadRole::EquationHead
                || arguments.iter().any(holds_equation_head)
        }
        TermKind::Injection { term, .. } => holds_equation_head(term),
        TermKind::List { heads, rest, .. } => {
            heads.iter().any(holds_equation_head)
                || rest.as_ref().is_some_and(|(middle, tail)| {
                    holds_equation_head(middle) || tail.iter().any(holds_equation_head)
                })
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().any(holds_equation_head)
                || rest.as_ref().is_some_and(holds_equation_head)
        }
        TermKind::Map { entries, rest, .. } => {
            entries
                .iter()
                .any(|(key, value)| holds_equation_head(key) || holds_equation_head(value))
                || rest.as_ref().is_some_and(holds_equation_head)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) | TermKind::And(..) => false,
    }
}

fn size(term: &Term) -> usize {
    1 + match term.kind() {
        TermKind::Application { arguments, .. } => arguments.iter().map(size).sum(),
        TermKind::Injection { term, .. } => size(term),
        TermKind::List { heads, rest, .. } => {
            heads.iter().map(size).sum::<usize>()
                + rest.as_ref().map_or(0, |(middle, tail)| {
                    size(middle) + tail.iter().map(size).sum::<usize>()
                })
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().map(size).sum::<usize>() + rest.as_ref().map_or(0, size)
        }
        TermKind::Map { entries, rest, .. } => {
            entries
                .iter()
                .map(|(key, value)| size(key) + size(value))
                .sum::<usize>()
                + rest.as_ref().map_or(0, size)
        }
        TermKind::And(left, right) => size(left) + size(right),
        TermKind::DomainValue { .. } | TermKind::Variable(_) => 0,
    }
}

thread_local! {
    /// Whether an evaluation of the current definition found a symbol declared `total` undefined
    /// on defined arguments (`Simplification::contradicted_total`).
    static CONTRADICTED_TOTAL: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Whether a call of the backend on the current definition stopped (its deadline passed or
    /// it ran out of stack) or panicked.
    static STOPPED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// `call`, a call of the backend; a panic in it is recorded as a stop ([`STOPPED`]) and decides
/// nothing.
fn guarded<T>(call: impl FnOnce() -> Option<T>) -> Option<T> {
    catch_unwind(AssertUnwindSafe(call)).unwrap_or_else(|_| {
        STOPPED.set(true);
        None
    })
}

/// The outcome of a simplification.
fn outcome(result: &Simplification) -> Outcome {
    if result.contradicted_total.is_some() {
        CONTRADICTED_TOTAL.set(true);
    }
    if result.undefined_term.is_some() {
        Outcome::Bottom
    } else if result.constraints().is_empty() && claimed_value(&result.term) {
        Outcome::Value(result.term.clone())
    } else {
        Outcome::Open
    }
}

/// The backend's evaluation of the ground term `term` in `definition`; a stop or a panic
/// decides nothing.
fn evaluate(definition: &BackendDefinition, term: &Term) -> Outcome {
    guarded(|| {
        let _deadline = deadline();
        match simplify(
            definition,
            term,
            SimplificationOptions {
                max_iterations: 64,
                ..SimplificationOptions::default()
            },
        ) {
            Ok(Ok(result)) => Some(outcome(&result)),
            Ok(Err(_)) => None,
            Err(stop) => {
                stop.into_cause();
                STOPPED.set(true);
                None
            }
        }
    })
    .unwrap_or(Outcome::Open)
}

/// The backend's simplification of the term `term` with variables, when it ends without
/// conditions.
fn simplified(definition: &BackendDefinition, term: &Term) -> Option<Term> {
    guarded(|| {
        let _deadline = deadline();
        match simplify(
            definition,
            term,
            SimplificationOptions {
                max_iterations: 64,
                ..SimplificationOptions::default()
            },
        ) {
            Ok(Ok(result))
                if result.constraints().is_empty() && result.undefined_term.is_none() =>
            {
                Some(result.term)
            }
            Ok(_) => None,
            Err(stop) => {
                stop.into_cause();
                STOPPED.set(true);
                None
            }
        }
    })
}

/// The backend's decision of `predicates` (their conjunction): `None` when it decides nothing.
fn decide(definition: &BackendDefinition, predicates: Vec<Predicate>) -> Option<bool> {
    if predicates.is_empty() {
        return Some(true);
    }
    guarded(|| {
        let _deadline = deadline();
        match simplify_predicate_with_solver(
            definition,
            &Predicate::And(predicates),
            &[],
            SimplificationOptions {
                max_iterations: 64,
                ..SimplificationOptions::default()
            },
            &NoSolver,
        ) {
            Ok(Ok(Predicate::True)) => Some(true),
            Ok(Ok(Predicate::False)) => Some(false),
            Ok(_) => None,
            Err(stop) => {
                stop.into_cause();
                STOPPED.set(true);
                None
            }
        }
    })
}

/// `term` read again from its KORE text in `definition`: the same term without the marks the
/// loaded definition's evaluation put on it, so that the definition without claims reads none.
fn reread(definition: &BackendDefinition, term: &Term) -> Option<Term> {
    definition
        .internalize_term(&crate::externalize::term(term), &[])
        .ok()
}

/// The ground `Int` literals the definition's executable equations mention, and 0 to 3.
fn literals(backend: &BackendDefinition) -> BTreeSet<i64> {
    fn collect(term: &Term, into: &mut BTreeSet<i64>) {
        match term.kind() {
            TermKind::DomainValue { sort, value } => {
                if *sort == Sort::simple("SortInt")
                    && let Some(number) = std::str::from_utf8(value.as_bytes())
                        .ok()
                        .and_then(|text| text.parse::<i64>().ok())
                {
                    into.insert(number);
                }
            }
            TermKind::Application { arguments, .. } => {
                for argument in arguments {
                    collect(argument, into);
                }
            }
            TermKind::Injection { term, .. } => collect(term, into),
            TermKind::And(left, right) => {
                collect(left, into);
                collect(right, into);
            }
            TermKind::List { heads, rest, .. } => {
                for item in heads {
                    collect(item, into);
                }
                if let Some((middle, tail)) = rest {
                    collect(middle, into);
                    for item in tail {
                        collect(item, into);
                    }
                }
            }
            TermKind::Set { elements, .. } => {
                for element in elements {
                    collect(element, into);
                }
            }
            TermKind::Map { entries, .. } => {
                for (key, value) in entries {
                    collect(key, into);
                    collect(value, into);
                }
            }
            TermKind::Variable(_) => {}
        }
    }
    let mut found = BTreeSet::from([0, 1, 2, 3]);
    for rule in executable_rules(backend) {
        collect(&rule.lhs, &mut found);
        if let RuleRhs::Term(rhs) = &rule.rhs {
            collect(rhs, &mut found);
        }
    }
    found
}

/// The literals of the builtin sorts the definition declares, as KORE.
fn literal_sources(backend: &BackendDefinition) -> Vec<String> {
    let mut sources = Vec::new();
    let sorts = backend.sorts();
    if sorts.contains_key("SortInt") {
        // The definition's own literals first, then 0 to 3.
        let (own, small): (Vec<i64>, Vec<i64>) = literals(backend)
            .into_iter()
            .partition(|value| !(0..=3).contains(value));
        sources.extend(
            own.into_iter()
                .chain(small)
                .take(6)
                .map(|value| format!(r#"\dv{{SortInt{{}}}}("{value}")"#)),
        );
    }
    if sorts.contains_key("SortBool") {
        sources.extend(["true", "false"].map(|value| format!(r#"\dv{{SortBool{{}}}}("{value}")"#)));
    }
    if sorts.contains_key("SortString") {
        sources.extend(["", "ab"].map(|value| format!(r#"\dv{{SortString{{}}}}("{value}")"#)));
    }
    sources
}

/// The values of `sort` and the injections of the values of its proper subsorts.
fn candidates(
    backend: &BackendDefinition,
    values: &BTreeMap<Sort, Vec<Term>>,
    sort: &Sort,
) -> Vec<Term> {
    let mut found = Vec::new();
    for (value_sort, terms) in values {
        if value_sort == sort {
            found.extend(terms.iter().cloned());
        } else if backend.sort_graph().check_subsort(value_sort, sort) == Ok(true) {
            found.extend(
                terms
                    .iter()
                    .map(|term| Term::injection(value_sort.clone(), sort.clone(), term.clone())),
            );
        }
    }
    found
}

/// The normal form of the ground term `term` when the backend leaves it unevaluated without
/// conditions and discharges its `\ceil`: an element the backend says is defined, although it
/// does not claim it as a value (a stuck application of a total function, say).
fn defined_normal_form(backend: &BackendDefinition, term: &Term) -> Option<Term> {
    let normal = simplified(backend, term)?;
    (normal.attributes().variables.is_empty()
        && decide(backend, vec![Predicate::Ceil(normal.clone())]) == Some(true))
    .then_some(normal)
}

/// The values the harness instantiates with, by sort: literals, then three rounds of every
/// symbol applied to values of its argument sorts, each application kept when the backend
/// evaluates it to a value it claims, or leaves it a normal form it says is defined.
fn values(backend: &BackendDefinition, rng: &mut Rng) -> BTreeMap<Sort, Vec<Term>> {
    let mut values = BTreeMap::<Sort, Vec<Term>>::new();
    let add = |values: &mut BTreeMap<Sort, Vec<Term>>, term: Term| {
        let entry = values.entry(term.sort()).or_default();
        if entry.len() < VALUES_PER_SORT && !entry.contains(&term) {
            entry.push(term);
        }
    };
    for source in literal_sources(backend) {
        if let Ok(pattern) = parse_pattern(&source)
            && let Ok(term) = backend.internalize_term(&pattern, &[])
        {
            add(&mut values, term);
        }
    }
    let symbols = backend
        .symbols()
        .values()
        .filter(|symbol| symbol.sort_variables.is_empty())
        .cloned()
        .collect::<Vec<_>>();
    for _round in 0..3 {
        for symbol in &symbols {
            if STOPPED.get() {
                return values;
            }
            for _ in 0..3 {
                let mut arguments = Vec::new();
                for sort in &symbol.argument_sorts {
                    let found = candidates(backend, &values, sort);
                    if found.is_empty() {
                        break;
                    }
                    arguments.push(rng.pick(&found).clone());
                }
                if arguments.len() != symbol.argument_sorts.len() {
                    break;
                }
                let application = Term::application(symbol.clone(), Vec::new(), arguments);
                if size(&application) > 10 {
                    continue;
                }
                let value = match evaluate(backend, &application) {
                    Outcome::Value(value) => Some(value),
                    Outcome::Bottom => None,
                    Outcome::Open => defined_normal_form(backend, &application),
                };
                if let Some(value) = value
                    && size(&value) <= 10
                {
                    add(&mut values, value);
                }
            }
        }
    }
    values
}

/// Whether the rule never applies to a ground term (`symbolic` on some variable).
fn symbolic(rule: &RewriteRule) -> bool {
    match &rule.attributes.concreteness {
        Concreteness::Unconstrained | Concreteness::All(ConstraintKind::Concrete) => false,
        Concreteness::All(ConstraintKind::Symbolic) => true,
        Concreteness::Some(constraints) => constraints
            .values()
            .any(|kind| *kind == ConstraintKind::Symbolic),
    }
}

/// The definition's executable equations, each once (a rule may sit at several indexes).
fn executable_rules(backend: &BackendDefinition) -> Vec<Arc<RewriteRule>> {
    let mut seen = BTreeSet::new();
    let mut rules = Vec::new();
    for groups in backend.function_theory().values() {
        for rule in groups.values().flatten() {
            if !rule.attributes.simplification
                && !symbolic(rule)
                && seen.insert(Arc::as_ptr(rule) as usize)
            {
                rules.push(rule.clone());
            }
        }
    }
    rules
}

/// `valuation` extended with the binding of every alias `\and(p, X)` of `pattern` to `p`'s
/// instance, innermost first.
fn bind_aliases(pattern: &Term, valuation: &mut Substitution) {
    match pattern.kind() {
        TermKind::And(left, right) => {
            bind_aliases(left, valuation);
            bind_aliases(right, valuation);
            for (alias, aliased) in [(right, left), (left, right)] {
                if let TermKind::Variable(variable) = alias.kind()
                    && !matches!(aliased.kind(), TermKind::Variable(_))
                {
                    let instance = substitute(aliased, valuation);
                    valuation.insert(variable.clone(), instance);
                }
            }
        }
        TermKind::Application { arguments, .. } => {
            for argument in arguments {
                bind_aliases(argument, valuation);
            }
        }
        TermKind::Injection { term, .. } => bind_aliases(term, valuation),
        TermKind::List { heads, rest, .. } => {
            for item in heads {
                bind_aliases(item, valuation);
            }
            if let Some((middle, tail)) = rest {
                bind_aliases(middle, valuation);
                for item in tail {
                    bind_aliases(item, valuation);
                }
            }
        }
        TermKind::Set { elements, .. } => {
            for element in elements {
                bind_aliases(element, valuation);
            }
        }
        TermKind::Map { entries, .. } => {
            for (key, value) in entries {
                bind_aliases(key, valuation);
                bind_aliases(value, valuation);
            }
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
    }
}

/// `term` with each `\and` of two equal conjuncts replaced by the conjunct; `None` when two
/// conjuncts differ (the valuation is no instance of an alias).
fn collapse(term: &Term) -> Option<Term> {
    match term.kind() {
        TermKind::And(left, right) => {
            let (left, right) = (collapse(left)?, collapse(right)?);
            (left == right).then_some(left)
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => Some(Term::application(
            symbol.clone(),
            sort_arguments.clone(),
            arguments.iter().map(collapse).collect::<Option<Vec<_>>>()?,
        )),
        TermKind::Injection {
            source,
            target,
            term,
        } => Some(Term::injection(
            source.clone(),
            target.clone(),
            collapse(term)?,
        )),
        _ => Some(term.clone()),
    }
}

/// The valuations of the variables `sampled` (each with its candidate values) an equation is
/// instantiated with: all of them when there are at most [`VALUATIONS`], otherwise
/// [`VALUATIONS`] distinct random ones.
fn valuations(sampled: &[(Variable, Vec<Term>)], rng: &mut Rng) -> Vec<Substitution> {
    let all = sampled.iter().try_fold(1usize, |product, (_, found)| {
        product.checked_mul(found.len())
    });
    if let Some(count) = all
        && count <= VALUATIONS
    {
        return (0..count)
            .map(|mut index| {
                sampled
                    .iter()
                    .map(|(variable, found)| {
                        let value = found[index % found.len()].clone();
                        index /= found.len();
                        (variable.clone(), value)
                    })
                    .collect()
            })
            .collect();
    }
    let mut drawn = BTreeSet::new();
    for _ in 0..VALUATIONS {
        drawn.insert(
            sampled
                .iter()
                .map(|(variable, found)| (variable.clone(), rng.pick(found).clone()))
                .collect::<Substitution>(),
        );
    }
    drawn.into_iter().collect()
}

/// Whether an equation of a priority group above `rule`'s applies at `instance`: `None` when
/// the backend's matcher or simplifier leaves it open.
fn higher_group_applies(
    backend: &BackendDefinition,
    rules: &[Arc<RewriteRule>],
    rule: &RewriteRule,
    instance: &Term,
) -> Option<bool> {
    let root = |term: &Term| match term.kind() {
        TermKind::Application { symbol, .. } => Some(symbol.name.clone()),
        _ => None,
    };
    for higher in rules.iter().filter(|higher| {
        higher.attributes.priority < rule.attributes.priority
            && root(&higher.lhs).is_none_or(|name| Some(name) == root(instance))
    }) {
        let result = guarded(|| {
            Some(match_terms_in_definition(
                MatchMode::Evaluate,
                backend,
                &higher.lhs,
                instance,
            ))
        })?;
        match result {
            MatchResult::Failed(_) => {}
            MatchResult::Success(substitution) => {
                let requires = higher
                    .requires
                    .instantiate(&substitution)
                    .with_definedness(backend, &[]);
                if decide(backend, requires)? {
                    return Some(true);
                }
            }
            MatchResult::Indeterminate { .. } => return None,
        }
    }
    Some(false)
}

/// A contradiction found at an instance, and whether it rests on no claim.
struct Contradiction {
    text: String,
    claim_free: bool,
}

/// What one definition's run collected.
#[derive(Default)]
struct Run {
    contradictions: Vec<Contradiction>,
    /// Ground terms evaluated with the claims, and their outcomes.
    evaluated: Vec<(Term, Outcome)>,
    /// Instances judged, for the generalizations.
    judged: Vec<Term>,
}

/// Whether `term` is a collection term: a list, map or set the collection laws build.
fn collection(term: &Term) -> bool {
    matches!(
        term.kind(),
        TermKind::List { .. } | TermKind::Map { .. } | TermKind::Set { .. }
    )
}

/// The left value of `instance`, and whether it is the hook's. At an application of a hooked
/// symbol whose hook applies it is the hook's result, which is what the symbol denotes there;
/// where the hook does not apply, the equations alone give the symbol's value, and the backend's
/// evaluation is the judge as at any other root. A collection term (the instance of a left-hand
/// side the collection laws normalize to a collection pattern or a bare variable) denotes itself
/// modulo those laws, so its value is the instance when it is a collection of claimed values
/// that repeats no key or element (one that does is `\bottom`, and is left undecided, as on the
/// right side); evaluating it would apply the equation under test to it.
fn left_value(backend: &BackendDefinition, instance: &Term, run: &mut Run) -> (Outcome, bool) {
    if collection(instance) {
        let outcome = if claimed_value(instance) {
            Outcome::Value(instance.clone())
        } else {
            Outcome::Open
        };
        return (outcome, true);
    }
    if let TermKind::Application { symbol, .. } = instance.kind()
        && symbol.attributes.hook.is_some()
    {
        let hooked = guarded(|| {
            let _deadline = deadline();
            Some(evaluate_in_definition(instance, backend))
        });
        let outcome = match hooked {
            Some(Ok(Ok(BuiltinResult::NotApplicable))) => None,
            Some(Ok(Ok(BuiltinResult::Value(value)))) if claimed_value(&value) => {
                Some(Outcome::Value(value))
            }
            Some(Ok(Ok(BuiltinResult::Bottom))) => Some(Outcome::Bottom),
            Some(Err(stop)) => {
                stop.into_cause();
                STOPPED.set(true);
                Some(Outcome::Open)
            }
            // A panic, recorded as a stop.
            None => Some(Outcome::Open),
            Some(Ok(_)) => Some(Outcome::Open),
        };
        if let Some(outcome) = outcome {
            return (outcome, true);
        }
    }
    let outcome = evaluate(backend, instance);
    run.evaluated.push((instance.clone(), outcome.clone()));
    (outcome, false)
}

/// The right value of an instance whose left value is a collection term: a collection right-hand
/// side is the collection of its separately evaluated parts, so that the equation under test is
/// not applied to its own result; any other term is evaluated. A part that is `\bottom` makes
/// the collection `\bottom`; a collection that repeats a key or an element after its parts are
/// evaluated, or keeps a rest, is left undecided.
fn collection_value(backend: &BackendDefinition, term: &Term, run: &mut Run) -> Outcome {
    fn parts(
        backend: &BackendDefinition,
        terms: &[Term],
        run: &mut Run,
    ) -> Result<Vec<Term>, Outcome> {
        let mut values = Vec::with_capacity(terms.len());
        for term in terms {
            match collection_value(backend, term, run) {
                Outcome::Value(value) => values.push(value),
                Outcome::Bottom => return Err(Outcome::Bottom),
                Outcome::Open => return Err(Outcome::Open),
            }
        }
        Ok(values)
    }
    let built = match term.kind() {
        TermKind::List {
            definition,
            heads,
            rest,
        } => {
            let (middle, tail) = match rest {
                Some((middle, tail)) => (vec![middle.clone()], tail.clone()),
                None => (Vec::new(), Vec::new()),
            };
            let (heads, middle, tail) = match (
                parts(backend, heads, run),
                parts(backend, &middle, run),
                parts(backend, &tail, run),
            ) {
                (Ok(heads), Ok(middle), Ok(tail)) => (heads, middle, tail),
                (Err(Outcome::Bottom), _, _)
                | (_, Err(Outcome::Bottom), _)
                | (_, _, Err(Outcome::Bottom)) => return Outcome::Bottom,
                _ => return Outcome::Open,
            };
            Term::list(
                definition.clone(),
                heads,
                middle.into_iter().next().map(|middle| (middle, tail)),
            )
        }
        TermKind::Map {
            definition,
            entries,
            rest,
        } => {
            let (keys, values): (Vec<Term>, Vec<Term>) = entries.iter().cloned().unzip();
            let rest = rest.iter().cloned().collect::<Vec<_>>();
            let (keys, values, rest) = match (
                parts(backend, &keys, run),
                parts(backend, &values, run),
                parts(backend, &rest, run),
            ) {
                (Ok(keys), Ok(values), Ok(rest)) => (keys, values, rest),
                (Err(Outcome::Bottom), _, _)
                | (_, Err(Outcome::Bottom), _)
                | (_, _, Err(Outcome::Bottom)) => return Outcome::Bottom,
                _ => return Outcome::Open,
            };
            Term::map(
                definition.clone(),
                keys.into_iter().zip(values).collect(),
                rest.into_iter().next(),
            )
        }
        TermKind::Set {
            definition,
            elements,
            rest,
        } => {
            let rest = rest.iter().cloned().collect::<Vec<_>>();
            let (elements, rest) = match (parts(backend, elements, run), parts(backend, &rest, run))
            {
                (Ok(elements), Ok(rest)) => (elements, rest),
                (Err(Outcome::Bottom), _) | (_, Err(Outcome::Bottom)) => return Outcome::Bottom,
                _ => return Outcome::Open,
            };
            Term::set(definition.clone(), elements, rest.into_iter().next())
        }
        _ => {
            let outcome = evaluate(backend, term);
            run.evaluated.push((term.clone(), outcome.clone()));
            return outcome;
        }
    };
    if claimed_value(&built) {
        Outcome::Value(built)
    } else {
        Outcome::Open
    }
}

/// Whether the backend discharges `\ceil(term)` through an equation head's claim.
fn defined_by_claim(backend: &BackendDefinition, term: &Term) -> bool {
    holds_equation_head(term) && decide(backend, vec![Predicate::Ceil(term.clone())]) == Some(true)
}

/// Draws the instances of every executable equation and judges each.
#[allow(
    clippy::too_many_lines,
    reason = "one pass over the instances of one definition"
)]
fn instances(
    label: &str,
    backend: &BackendDefinition,
    values: &BTreeMap<Sort, Vec<Term>>,
    rng: &mut Rng,
    tally: &mut AxiomTally,
) -> Run {
    let mut run = Run::default();
    let rules = executable_rules(backend);
    for rule in &rules {
        if STOPPED.get() {
            break;
        }
        let rhs = match &rule.rhs {
            RuleRhs::Term(rhs) => Some(rhs),
            RuleRhs::Bottom => None,
            RuleRhs::Disjunction(_) | RuleRhs::Top | RuleRhs::Predicates(_) => continue,
        };
        let variables = rule.lhs.attributes().variables.clone();
        let mut free = rhs.map_or_else(BTreeSet::new, |rhs| rhs.attributes().variables.clone());
        for predicate in rule.requires.iter().chain(rule.ensures.iter()) {
            free.extend(predicate.free_variables());
        }
        if !rule.existentials.is_empty() || !free.is_subset(&variables) {
            continue;
        }
        let aliases = aliases_of(&rule.lhs);
        let sampled = variables
            .iter()
            .filter(|variable| !aliases.contains(*variable))
            .map(|variable| {
                (
                    variable.clone(),
                    candidates(backend, values, &variable.sort),
                )
            })
            .collect::<Vec<_>>();
        if sampled.iter().any(|(_, found)| found.is_empty()) {
            continue;
        }
        tally.equations += 1;
        for mut valuation in valuations(&sampled, rng) {
            if STOPPED.get() {
                break;
            }
            bind_aliases(&rule.lhs, &mut valuation);
            let Some(instance) = collapse(&substitute(&rule.lhs, &valuation)) else {
                continue;
            };
            let requires = rule
                .requires
                .instantiate(&valuation)
                .with_definedness(backend, &[]);
            match decide(backend, requires) {
                Some(true) => {}
                Some(false) => continue,
                None => {
                    tally.undecided += 1;
                    continue;
                }
            }
            match higher_group_applies(backend, &rules, rule, &instance) {
                Some(false) => {}
                Some(true) => continue,
                None => {
                    tally.undecided += 1;
                    continue;
                }
            }
            let ensures = if rule.ensures.is_empty() {
                Some(true)
            } else {
                decide(
                    backend,
                    rule.ensures
                        .instantiate(&valuation)
                        .with_definedness(backend, &[]),
                )
            };
            tally.instances += 1;
            let right = match (rhs, ensures) {
                (_, None) => {
                    tally.undecided += 1;
                    continue;
                }
                (None, _) | (_, Some(false)) => Outcome::Bottom,
                (Some(rhs), Some(true)) if collection(&instance) => {
                    collection_value(backend, &substitute(rhs, &valuation), &mut run)
                }
                (Some(rhs), Some(true)) => {
                    let right = substitute(rhs, &valuation);
                    let outcome = evaluate(backend, &right);
                    run.evaluated.push((right, outcome.clone()));
                    outcome
                }
            };
            let (left, hooked) = left_value(backend, &instance, &mut run);
            if std::env::var_os("KRUST_DEFINEDNESS_ORACLE_VERBOSE").is_some() {
                eprintln!(
                    "{label}: {} = {} by {}: {} and {}",
                    show(&instance),
                    rhs.map_or_else(
                        || r"\bottom".to_owned(),
                        |rhs| show(&substitute(rhs, &valuation))
                    ),
                    rule_name(rule),
                    left.show(),
                    right.show()
                );
            }
            // A side the backend leaves open contradicts `\bottom` on the other only through
            // a `\ceil` discharge it makes by a claim.
            let (left_defined, right_defined) = match (&left, &right) {
                (Outcome::Open, Outcome::Bottom) => (defined_by_claim(backend, &instance), false),
                (Outcome::Bottom, Outcome::Open) if rhs.is_some() => (
                    false,
                    rhs.is_some_and(|rhs| defined_by_claim(backend, &substitute(rhs, &valuation))),
                ),
                _ => (false, false),
            };
            if !(left.decided() && right.decided()) && !left_defined && !right_defined {
                tally.undecided += 1;
                continue;
            }
            tally.compared += 1;
            tally.hooked += usize::from(hooked);
            run.judged.push(instance.clone());
            if contradict(&left, &right) || left_defined || right_defined {
                // Against `\bottom` only the definedness of the valuation is at stake.
                let definedness_only =
                    matches!(left, Outcome::Bottom) || matches!(right, Outcome::Bottom);
                let claim_free = !left_defined
                    && !right_defined
                    && valuation
                        .values()
                        .all(|value| claim_free(backend, value, definedness_only))
                    && [&left, &right].into_iter().all(|side| match side {
                        Outcome::Value(value) => claim_free(backend, value, false),
                        Outcome::Bottom => true,
                        Outcome::Open => false,
                    });
                let shown = |outcome: &Outcome, defined: bool| {
                    if defined {
                        "a term whose \\ceil is discharged".to_owned()
                    } else {
                        outcome.show()
                    }
                };
                run.contradictions.push(Contradiction {
                    text: format!(
                        "{label}: the instance {} of {} (at {}) has the left value {}{} and the right value {}",
                        show(&instance),
                        rule_name(rule),
                        valuation
                            .iter()
                            .map(|(variable, value)| format!("{} := {}", variable.name, show(value)))
                            .collect::<Vec<_>>()
                            .join(", "),
                        shown(&left, left_defined),
                        if hooked { " (the hook's)" } else { "" },
                        shown(&right, right_defined),
                    ),
                    claim_free,
                });
            }
        }
    }
    run
}

fn rule_name(rule: &RewriteRule) -> String {
    rule.attributes
        .label
        .clone()
        .unwrap_or_else(|| rule.attributes.unique_id.clone())
}

/// The variables an alias `\and(p, X)` of `pattern` binds.
fn aliases_of(pattern: &Term) -> BTreeSet<Variable> {
    let mut found = BTreeSet::new();
    let mut pending = vec![pattern];
    while let Some(term) = pending.pop() {
        match term.kind() {
            TermKind::And(left, right) => {
                for side in [left, right] {
                    if let TermKind::Variable(variable) = side.kind() {
                        found.insert(variable.clone());
                    }
                }
                pending.push(left);
                pending.push(right);
            }
            TermKind::Application { arguments, .. } => pending.extend(arguments),
            TermKind::Injection { term, .. } => pending.push(term),
            TermKind::List { heads, rest, .. } => {
                pending.extend(heads);
                if let Some((middle, tail)) = rest {
                    pending.push(middle);
                    pending.extend(tail);
                }
            }
            TermKind::Set { elements, .. } => pending.extend(elements),
            TermKind::Map { entries, .. } => {
                for (key, value) in entries {
                    pending.push(key);
                    pending.push(value);
                }
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
    }
    found
}

/// Withheld claims: no result the definition without claims decides is contradicted by the
/// loaded one's.
fn withheld(
    label: &str,
    backend: &BackendDefinition,
    without: &BackendDefinition,
    run: &Run,
    tally: &mut AxiomTally,
) {
    let mut seen = BTreeSet::new();
    for (term, with) in &run.evaluated {
        if !seen.insert(term.clone()) {
            continue;
        }
        let Some(plain) = reread(without, term) else {
            continue;
        };
        let decided = evaluate(without, &plain);
        let agrees = match (&decided, with) {
            (Outcome::Open, _) => continue,
            (Outcome::Value(plain_value), Outcome::Value(value)) => {
                reread(backend, plain_value).is_some_and(|plain_value| plain_value == *value)
            }
            (Outcome::Bottom, Outcome::Bottom) | (_, Outcome::Open) => true,
            (Outcome::Value(_), Outcome::Bottom) | (Outcome::Bottom, Outcome::Value(_)) => false,
        };
        tally.withheld_decided += 1;
        if !agrees {
            tally.failures.push(format!(
                "{label}: {} is {} with every claim withheld and {} with the claims",
                show(term),
                decided.show(),
                with.show()
            ));
        }
    }
}

/// Decisions about terms with variables: each judged instance with one of its first two
/// arguments replaced by a variable, against its values.
fn generalizations(
    label: &str,
    backend: &BackendDefinition,
    values: &BTreeMap<Sort, Vec<Term>>,
    run: &Run,
    tally: &mut AxiomTally,
) {
    let mut seen = BTreeSet::new();
    for instance in &run.judged {
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = instance.kind()
        else {
            continue;
        };
        if symbol.attributes.hook.is_some() {
            continue;
        }
        for (position, sort) in symbol.argument_sorts.iter().enumerate().take(2) {
            let variable = Variable::new(format!("VarGen{position}"), sort.clone());
            let mut generalized_arguments = arguments.clone();
            generalized_arguments[position] = Term::variable(variable.clone());
            let generalized = Term::application(
                symbol.clone(),
                sort_arguments.clone(),
                generalized_arguments,
            );
            if !seen.insert(generalized.clone()) {
                continue;
            }
            let token =
                guarded(|| Some(backend.instance_normal(&generalized).is_some())).unwrap_or(false);
            let defined = holds_equation_head(&generalized)
                && decide(backend, vec![Predicate::Ceil(generalized.clone())]) == Some(true);
            let reduct = simplified(backend, &generalized).filter(|reduct| *reduct != generalized);
            if !token && !defined && reduct.is_none() {
                continue;
            }
            let mut checked = false;
            for value in candidates(backend, values, sort)
                .into_iter()
                .take(GENERALIZED_VALUES)
            {
                let valuation = Substitution::from([(variable.clone(), value.clone())]);
                let ground = substitute(&generalized, &valuation);
                let evaluated = evaluate(backend, &ground);
                let mut fail = |what: String| {
                    tally.failures.push(format!(
                        "{label}: {} is {what}, but at {} := {} it evaluates to {}",
                        show(&generalized),
                        variable.name,
                        show(&value),
                        evaluated.show()
                    ));
                };
                if token {
                    checked = true;
                    match &evaluated {
                        Outcome::Value(result) if *result != ground => {
                            fail("instance-normal".into());
                        }
                        Outcome::Bottom => fail("instance-normal".into()),
                        Outcome::Value(_) | Outcome::Open => {}
                    }
                }
                if defined {
                    checked = true;
                    if matches!(evaluated, Outcome::Bottom) {
                        fail("defined (its \\ceil is discharged)".into());
                    }
                }
                if let Some(reduct) = &reduct {
                    let other = evaluate(backend, &substitute(reduct, &valuation));
                    if evaluated.decided() && other.decided() {
                        checked = true;
                        if contradict(&evaluated, &other) {
                            fail(format!(
                                "simplified to {}, whose instance evaluates to {}",
                                show(reduct),
                                other.show()
                            ));
                        }
                    }
                }
            }
            tally.generalizations += usize::from(checked);
        }
    }
}

/// Runs the harness on one loaded definition.
pub(super) fn check_axioms(
    label: &str,
    backend: &BackendDefinition,
    reordered: Option<&BackendDefinition>,
    rng: &mut Rng,
) -> AxiomTally {
    let mut tally = AxiomTally {
        definitions: 1,
        ..AxiomTally::default()
    };
    CONTRADICTED_TOTAL.set(false);
    STOPPED.set(false);
    check_claims(label, backend, reordered, rng, &mut tally);
    // A definition with an evaluation that does not end within the bounds is outside the
    // contract (precondition P0, stated and not checked): its claims get no guarantee, and the
    // harness stops at the first such evaluation.
    if STOPPED.get() {
        tally.outside_termination = 1;
        tally.without_model = 0;
        tally.failures.clear();
        return tally;
    }
    // A definition with a `total` symbol undefined on defined arguments is outside the contract
    // (precondition P2, stated and not checked): its claims get no guarantee.
    if CONTRADICTED_TOTAL.get() {
        tally.outside_totality = 1;
        tally.failures.clear();
    }
    tally
}

/// Whether some claim of `backend` can be withdrawn by a pair: it declares an equation head, or
/// an overloaded symbol that is neither a free constructor nor hooked. Otherwise the check
/// classifies no pair, since none can change a claim (`docs/compatibility.md`, "Anywhere
/// rules").
fn claims_rest_on_pairs(backend: &BackendDefinition) -> bool {
    backend
        .symbols()
        .values()
        .any(|symbol| claimable(backend, symbol))
}

/// Whether no executable equation of `definition` can match any application in the ground term
/// `term`, by the backend's own matcher: `term` is then a normal form whether or not the backend
/// claims it as a value. An equation indexed at a collection or a bare variable could match
/// anywhere, so with one nothing is shown.
fn shown_normal(definition: &BackendDefinition, term: &Term) -> bool {
    let rules = executable_rules(definition);
    if rules
        .iter()
        .any(|rule| !matches!(rule.lhs.kind(), TermKind::Application { .. }))
    {
        return false;
    }
    let mut pending = vec![term.clone()];
    while let Some(term) = pending.pop() {
        match term.kind() {
            TermKind::Application {
                symbol, arguments, ..
            } => {
                for rule in &rules {
                    let TermKind::Application { symbol: root, .. } = rule.lhs.kind() else {
                        continue;
                    };
                    if root.name != symbol.name {
                        continue;
                    }
                    let result = guarded(|| {
                        Some(match_terms_in_definition(
                            MatchMode::Evaluate,
                            definition,
                            &rule.lhs,
                            &term,
                        ))
                    });
                    if !matches!(result, Some(MatchResult::Failed(_))) {
                        return false;
                    }
                }
                pending.extend(arguments.iter().cloned());
            }
            TermKind::Injection { term, .. } => pending.push(term.clone()),
            TermKind::List { heads, rest, .. } => {
                pending.extend(heads.iter().cloned());
                if let Some((middle, tail)) = rest {
                    pending.push(middle.clone());
                    pending.extend(tail.iter().cloned());
                }
            }
            TermKind::Set { elements, rest, .. } => {
                pending.extend(elements.iter().cloned());
                pending.extend(rest.iter().cloned());
            }
            TermKind::Map { entries, rest, .. } => {
                for (key, value) in entries {
                    pending.push(key.clone());
                    pending.push(value.clone());
                }
                pending.extend(rest.iter().cloned());
            }
            TermKind::DomainValue { .. } => {}
            TermKind::Variable(_) | TermKind::And(..) => return false,
        }
    }
    true
}

/// The normal form the backend evaluates the ground term `term` to in `definition`, printed
/// (`\bottom` for an undefined one): a value it claims, or a term no executable equation can
/// match ([`shown_normal`]); `None` otherwise, or when the evaluation ends with conditions or not
/// at all.
fn normal_form(definition: &BackendDefinition, term: &Term) -> Option<String> {
    guarded(|| {
        let _deadline = deadline();
        match simplify(
            definition,
            term,
            SimplificationOptions {
                max_iterations: 64,
                ..SimplificationOptions::default()
            },
        ) {
            Ok(Ok(result)) if result.undefined_term.is_some() => Some(r"\bottom".to_owned()),
            Ok(Ok(result))
                if result.constraints().is_empty()
                    && (claimed_value(&result.term) || shown_normal(definition, &result.term)) =>
            {
                Some(show(&result.term))
            }
            Ok(_) => None,
            Err(stop) => {
                stop.into_cause();
                STOPPED.set(true);
                None
            }
        }
    })
}

/// Whether the full check accepts `backend`: it classifies pairs, and names none and no
/// violated precondition row.
fn accepted(backend: &BackendDefinition) -> bool {
    let full = backend.value_claims_in_scope(crate::confluence::CheckScope::All);
    claims_rest_on_pairs(backend) && full.unjoined().is_empty() && full.violations().is_empty()
}

/// Equation order: a definition the full check accepts gives every ground term one normal form
/// (every peak joins), so the order its axioms are written in, which decides the order the
/// evaluator tries the equations of one priority group in, changes no result. `reordered` is the
/// definition with its axioms in another order.
fn equation_order(
    label: &str,
    backend: &BackendDefinition,
    reordered: &BackendDefinition,
    run: &Run,
    tally: &mut AxiomTally,
) {
    if !(accepted(backend) && accepted(reordered)) {
        return;
    }
    let mut seen = BTreeSet::new();
    for (term, _) in &run.evaluated {
        if !seen.insert(term.clone()) {
            continue;
        }
        let Some(other) = reread(reordered, term) else {
            continue;
        };
        let (Some(one), Some(two)) = (normal_form(backend, term), normal_form(reordered, &other))
        else {
            continue;
        };
        tally.reordered += 1;
        if one != two {
            tally.failures.push(format!(
                "{label}: the check accepts the definition, but {} evaluates to {one} in one order of its axioms and to {two} in another",
                show(term)
            ));
        }
    }
}

fn check_claims(
    label: &str,
    backend: &BackendDefinition,
    reordered: Option<&BackendDefinition>,
    rng: &mut Rng,
    tally: &mut AxiomTally,
) {
    let values = values(backend, rng);
    let run = instances(label, backend, &values, rng, tally);
    if STOPPED.get() {
        return;
    }
    if let Some(reordered) = reordered {
        equation_order(label, backend, reordered, &run, tally);
    }
    if let Some(proof) = run
        .contradictions
        .iter()
        .find(|contradiction| contradiction.claim_free)
    {
        let full = backend.value_claims_in_scope(crate::confluence::CheckScope::All);
        if claims_rest_on_pairs(backend)
            && full.unjoined().is_empty()
            && full.violations().is_empty()
        {
            tally.failures.push(format!(
                "{}; it rests on no claim, so the definition has no model, but the check names no pair",
                proof.text
            ));
        } else {
            tally.without_model = 1;
        }
        return;
    }
    for contradiction in &run.contradictions {
        tally.failures.push(format!(
            "{}: the axiom makes them equal, so a claim the backend makes holds in no model",
            contradiction.text
        ));
    }
    let without = backend.with_claims_withheld();
    withheld(label, backend, &without, &run, tally);
    generalizations(label, backend, &values, &run, tally);
}

/// Loads `definition` and runs the harness on it, comparing evaluations with the definition
/// whose axioms are written in the reverse order.
pub(super) fn check_definition(label: &str, definition: &Definition, rng: &mut Rng) -> AxiomTally {
    let mut reversed = definition.clone();
    reversed.equations.reverse();
    match (backend(definition), backend(&reversed)) {
        (Ok(loaded), Ok(reordered)) => check_axioms(label, &loaded, Some(&reordered), rng),
        (Err(error), _) | (_, Err(error)) => AxiomTally {
            definitions: 1,
            rejected: 1,
            failures: vec![format!("{label}: rejected: {error}")],
            ..AxiomTally::default()
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A set that holds a claimed value twice is `\bottom`, so it is no claimed value, though
    /// each of its elements is one; with the element once it is one.
    #[test]
    fn a_collection_that_repeats_an_element_is_no_claimed_value() {
        let definition = super::super::language::Definition::new(&["A"]).with_collections();
        let backend = backend(&definition).expect("the definition loads");
        let pattern = parse_pattern(r"setItem{}(mv0{}())").expect("the pattern parses");
        let term = backend
            .internalize_term(&pattern, &[])
            .expect("the pattern internalizes");
        let Outcome::Value(single) = evaluate(&backend, &term) else {
            panic!("`setItem(mv0)` evaluates to a value")
        };
        let TermKind::Set {
            definition: set,
            elements,
            ..
        } = single.kind()
        else {
            panic!("`setItem(mv0)` evaluates to a set")
        };
        assert!(claimed_value(&single));
        let repeated = Term::set(Arc::clone(set), vec![elements[0].clone(); 2], None);
        assert!(repeated.repeated_collection_key().is_some());
        assert!(!claimed_value(&repeated));
    }

    /// A panic in a backend call is recorded as a stop, so the definition is counted outside P0
    /// instead of its instance being skipped as undecided.
    #[test]
    fn a_panic_in_a_backend_call_is_a_stop() {
        STOPPED.set(false);
        assert_eq!(
            guarded(|| -> Option<()> { panic!("a backend call panics") }),
            None
        );
        assert!(STOPPED.get());
        STOPPED.set(false);
        assert_eq!(guarded(|| Some(1)), Some(1));
        assert!(!STOPPED.get());
    }
}
