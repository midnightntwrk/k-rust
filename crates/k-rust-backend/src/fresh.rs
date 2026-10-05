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
//! mode = "avoid-set construction at a site (freshen_existentials, mint_unbound_rule_variables, freshen_claim, rename_apart); an alias binder renamed to avoid capture looks its candidates up in the names of its alias body, laid out at load, and in the free variables of the arguments substituted under it, computed once per unfolding (alias Expander::rename_to_avoid_capture)"
//! bound = "O(v log v) per call before the retry loop"
//!
//! [[cost]]
//! mode = "state and solution keys (RequestNames::state_key, RequestNames::solution_key)"
//! bound = "per refinement pass O(n + v log v) for an object of n nodes and v variables, plus labelling and sorting each map, set, conjunction or disjunction of k elements holding a variable not yet numbered, O(size + k log k); at most v + 1 passes, usually one or two; where passes leave tied elements, a search that numbers one more variable and refines again, at most v times along a path, completing at most 32 numberings (LEAF_BUDGET) with an O(n) key each, and checking at most 1024 exchanges of two variables (EXCHANGE_CHECKS), O(n) each"
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
    collections::{BTreeMap, BTreeSet},
    hash::{DefaultHasher, Hash, Hasher},
    sync::Arc,
};

use rustc_hash::FxHashMap;

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
    /// other variables: the pattern under [`RequestNames::canonical`]'s renaming, its
    /// constraints sorted (a conjunction, so their order does not change what the state
    /// denotes).
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
    /// Conversely, two such renamings of one state have equal keys, except where
    /// [`RequestNames::canonical`] gives up its search.
    pub(crate) fn state_key(&self, pattern: &Pattern) -> Pattern {
        let object = Object {
            variables: &[],
            terms: &[&pattern.term],
            predicates: &pattern.constraints,
        };
        let (term, constraints) = self.canonical(&object, |renaming| {
            (
                renaming.term(&pattern.term),
                renaming.constraints(&pattern.constraints),
            )
        });
        Pattern { term, constraints }
    }

    /// A solution of a pattern search, the substitution of the target's variables and the
    /// constraints under which the state matches, whatever names the request's counter gave the
    /// state's other variables: both under one renaming of [`RequestNames::canonical`], the
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
        let object = Object {
            variables: &bound,
            terms: &values,
            predicates: constraints,
        };
        self.canonical(&object, |renaming| {
            let substitution = substitution
                .iter()
                .map(|(variable, value)| (renaming.variable(variable), renaming.term(value)))
                .collect();
            (substitution, renaming.constraints(constraints))
        })
    }

    /// The least `key` of `object` under the canonical numberings of the variables of
    /// `object` (free or bound) that no variable of the request is spelled as: each such
    /// variable renamed to `!{index}`, its position in a numbering. No name of the backend has
    /// an empty base (`term::names`), so `!{index}` captures no variable of them.
    ///
    /// The result must not depend on the names it replaces, so that every injective renaming
    /// of those variables gets one key. A numbering is built by [`Numbering::refine`]: the
    /// variables in order of first occurrence, visiting the elements of a map or a set and the
    /// operands of a conjunction or a disjunction (stored in an order that compares names) in
    /// the order of a label that sees a renamed variable only through its kind, its sort and
    /// its number, if it has one. Elements whose labels tie are passed over until the numbers
    /// their variables receive elsewhere tell them apart. When nothing more tells tied
    /// elements apart, the search numbers next, in turn, each variable that occurs in the
    /// first such group, skipping a variable whose exchange with one already tried maps
    /// `object` to itself (it leads to the same keys), and keeps the least key of the
    /// numberings this completes ([`Numbering::search`]). Every step depends only on the
    /// structure of `object` and on the numbers given so far, so a renaming of `object`
    /// builds the renamed numberings and the same least key.
    ///
    /// The search stops after [`LEAF_BUDGET`] complete numberings; the numbering is then
    /// completed by visiting tied elements in their stored order, which compares names, so
    /// two renamings of such an `object` can keep different keys. Any key is `object` under an
    /// injective renaming that fixes the request's names, so equal keys never identify two
    /// objects that are not renamings of each other.
    fn canonical<K: Ord>(&self, object: &Object<'_>, key: impl Fn(&CanonicalRenaming) -> K) -> K {
        let renamable = object
            .all_variables()
            .into_iter()
            .filter(|variable| self.renames(variable))
            .collect::<BTreeSet<_>>();
        if renamable.is_empty() {
            return key(&CanonicalRenaming::default());
        }
        let mut root = Numbering {
            renamable: &renamable,
            index: BTreeMap::new(),
            order: Vec::new(),
        };
        let Some(candidates) = root.refine(object) else {
            return key(&root.renaming());
        };
        let mut search = Search {
            object,
            leaves: 0,
            exchange_checks: 0,
            class: BTreeMap::new(),
        };
        if let Some(least) = root.clone().search(candidates, &mut search, &key) {
            return least;
        }
        let mut pass = Pass::new(&mut root, true);
        pass.object(object);
        key(&root.renaming())
    }

    /// Whether the key renames `variable`: no variable of the request is spelled as it is.
    fn renames(&self, variable: &Variable) -> bool {
        !self.spells(&variable.name)
    }
}

/// The most complete numberings [`Numbering::search`] builds before [`RequestNames::canonical`]
/// falls back to stored order.
const LEAF_BUDGET: usize = 32;

/// The most exchanges of two variables [`Numbering::search`] checks
/// ([`Object::exchange_fixes`]); past it, candidates are tried without that pruning.
const EXCHANGE_CHECKS: usize = 1024;

/// The key of a pattern-search solution ([`RequestNames::solution_key`]).
pub(crate) type SolutionKey = (Substitution, Vec<Predicate>);

/// What a key is built over: variables, then terms, in a fixed order, then constraints, a
/// conjunction.
struct Object<'a> {
    variables: &'a [&'a Variable],
    terms: &'a [&'a Term],
    predicates: &'a [Predicate],
}

impl Object<'_> {
    /// Every variable of the object, free or bound.
    fn all_variables(&self) -> BTreeSet<Variable> {
        let mut variables = self
            .variables
            .iter()
            .map(|variable| (*variable).clone())
            .collect::<BTreeSet<_>>();
        for term in self.terms {
            variables.extend(term.attributes().variables.iter().cloned());
        }
        collect_all_variables(self.predicates, &mut variables);
        variables
    }

    /// Whether exchanging `first` and `second`, two variables of one kind and sort, maps the
    /// object to itself: the variables are left in place, every term is unchanged, and the
    /// constraints are the same set.
    fn exchange_fixes(&self, first: &Variable, second: &Variable) -> bool {
        if self
            .variables
            .iter()
            .any(|variable| *variable == first || *variable == second)
        {
            return false;
        }
        let exchange = Substitution::from([
            (first.clone(), Term::variable(second.clone())),
            (second.clone(), Term::variable(first.clone())),
        ]);
        self.terms
            .iter()
            .all(|term| substitute(term, &exchange) == **term)
            && {
                let exchanged = rename_predicates(self.predicates, |variable| {
                    if variable == first {
                        second.clone()
                    } else if variable == second {
                        first.clone()
                    } else {
                        variable.clone()
                    }
                });
                conjunction_set(exchanged) == conjunction_set(self.predicates.to_vec())
            }
    }
}

/// `predicates`, a conjunction, as a set: the operands of every conjunction and disjunction
/// and the predicates themselves sorted and deduplicated.
fn conjunction_set(mut predicates: Vec<Predicate>) -> Vec<Predicate> {
    for predicate in &mut predicates {
        sort_operands(predicate);
    }
    predicates.sort();
    predicates.dedup();
    predicates
}

/// A numbering, possibly partial, of the variables a key renames.
#[derive(Clone)]
struct Numbering<'r> {
    /// The variables the key renames.
    renamable: &'r BTreeSet<Variable>,
    /// The number of each numbered variable: its position in `order`.
    index: BTreeMap<Variable, usize>,
    /// The numbered variables, in the order of their numbers.
    order: Vec<Variable>,
}

impl Numbering<'_> {
    /// Whether `variable` is renamed and not yet numbered.
    fn pending(&self, variable: &Variable) -> bool {
        self.renamable.contains(variable) && !self.index.contains_key(variable)
    }

    fn term_pending(&self, term: &Term) -> bool {
        term.attributes()
            .variables
            .iter()
            .any(|variable| self.pending(variable))
    }

    fn predicate_pending(&self, predicate: &Predicate) -> bool {
        let mut variables = BTreeSet::new();
        collect_all_variables(std::iter::once(predicate), &mut variables);
        variables.iter().any(|variable| self.pending(variable))
    }

    /// Give `variable` the next number, if it is renamed and has none.
    fn number(&mut self, variable: &Variable) {
        if self.pending(variable) {
            self.index.insert(variable.clone(), self.order.len());
            self.order.push(variable.clone());
        }
    }

    /// Number what the object's structure orders: repeat passes ([`Pass`]) while one gives a
    /// new number. `None` when every renamed variable is numbered; otherwise the variables,
    /// not yet numbered, of the first group of elements no pass could order.
    ///
    /// Each pass numbers at least one variable or is the last, so there are at most one more
    /// passes than renamed variables; a pass that leaves no group behind is the last.
    fn refine(&mut self, object: &Object<'_>) -> Option<Vec<Variable>> {
        loop {
            let before = self.order.len();
            let mut pass = Pass::new(self, false);
            pass.object(object);
            let stuck = pass.stuck;
            match stuck {
                None => return None,
                Some(candidates) if self.order.len() == before => return Some(candidates),
                Some(_) => {}
            }
        }
    }

    /// The least key over the numberings that complete this one by numbering next one of
    /// `candidates`, then refining, recursively; `None` once more than [`LEAF_BUDGET`]
    /// numberings were completed in all.
    ///
    /// Only one of each class of candidates that exchanges map into each other is tried
    /// ([`Search::representatives`]): such an exchange maps the object to itself and fixes
    /// every numbered variable, so it maps the numberings that start with one candidate to
    /// those that start with the other, and both give the same keys. The search recurses only
    /// where it branches, so at most [`LEAF_BUDGET`] times along a path.
    fn search<K: Ord>(
        mut self,
        mut candidates: Vec<Variable>,
        search: &mut Search<'_, '_>,
        key: &impl Fn(&CanonicalRenaming) -> K,
    ) -> Option<K> {
        loop {
            let representatives = search.representatives(candidates);
            if let [only] = representatives.as_slice() {
                self.number(only);
                match self.refine(search.object) {
                    Some(next) => {
                        candidates = next;
                        continue;
                    }
                    None => return self.leaf(search, key),
                }
            }
            let mut least: Option<K> = None;
            for candidate in &representatives {
                let mut branch = self.clone();
                branch.number(candidate);
                let found = match branch.refine(search.object) {
                    Some(next) => branch.search(next, search, key)?,
                    None => branch.leaf(search, key)?,
                };
                if least.as_ref().is_none_or(|least| found < *least) {
                    least = Some(found);
                }
            }
            return least;
        }
    }

    /// The key of this complete numbering, counted; `None` past [`LEAF_BUDGET`].
    fn leaf<K>(
        &self,
        search: &mut Search<'_, '_>,
        key: &impl Fn(&CanonicalRenaming) -> K,
    ) -> Option<K> {
        search.leaves += 1;
        (search.leaves <= LEAF_BUDGET).then(|| key(&self.renaming()))
    }

    fn renaming(&self) -> CanonicalRenaming {
        let renaming = self
            .order
            .iter()
            .enumerate()
            .map(|(index, variable)| (variable.clone(), variable.with_name(format!("!{index}"))))
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
}

/// What one [`Numbering::search`] has used, and the classes of variables whose exchange it
/// found to map the object to itself.
struct Search<'o, 'a> {
    object: &'o Object<'a>,
    /// Complete numberings built.
    leaves: usize,
    /// Exchanges checked.
    exchange_checks: usize,
    /// The classes found so far, as chains: each variable found exchangeable with another
    /// points to a variable of its class; the end of the chain stands for the class.
    class: BTreeMap<Variable, Variable>,
}

impl Search<'_, '_> {
    /// `candidates` without each one whose exchange with a kept one maps the object to itself.
    ///
    /// Such exchanges, which depend on the object alone, are an equivalence (two of them
    /// compose to the third), so a candidate in the class of a kept one is dropped without a
    /// check, and one candidate of each class is kept. Past [`EXCHANGE_CHECKS`] checks, a
    /// candidate not known to be in a kept one's class is kept: trying more candidates than
    /// needed changes the cost, not the least key.
    fn representatives(&mut self, candidates: Vec<Variable>) -> Vec<Variable> {
        debug_assert!(
            !candidates.is_empty(),
            "a tied group holds a pending variable"
        );
        let mut kept: Vec<Variable> = Vec::new();
        for candidate in candidates {
            let class = self.class_of(&candidate).clone();
            if kept.iter().any(|kept| *self.class_of(kept) == class) {
                continue;
            }
            let mut exchangeable = None;
            for kept in &kept {
                if self.exchange_checks >= EXCHANGE_CHECKS {
                    break;
                }
                if kept.kind != candidate.kind || kept.sort != candidate.sort {
                    continue;
                }
                self.exchange_checks += 1;
                if self.object.exchange_fixes(kept, &candidate) {
                    exchangeable = Some(self.class_of(kept).clone());
                    break;
                }
            }
            match exchangeable {
                // Join the candidate's class to the kept one's; `first` is no variable of
                // the candidate's class, so the classes stay chains that end.
                Some(first) => {
                    self.class.insert(class, first);
                }
                None => kept.push(candidate),
            }
        }
        kept
    }

    /// The variable that stands for `variable`'s class as found so far.
    fn class_of<'v>(&'v self, mut variable: &'v Variable) -> &'v Variable {
        // An entry is added only from the end of one chain to the end of another.
        while let Some(earlier) = self.class.get(variable) {
            variable = earlier;
        }
        variable
    }
}

/// One walk of an object that numbers its pending variables in order of first occurrence.
///
/// Terms are walked in preorder; a subterm with no pending variable is skipped. The
/// elements of a map or a set and the operands of a conjunction or a disjunction that hold a
/// pending variable are walked in the order of their labels ([`Pass::label`]), computed with
/// the numbers given before the pass began. Elements whose labels tie form a group that the
/// pass leaves for a later pass (recording the pending variables of the first such group), or,
/// for the stored-order completion, walks in stored order.
struct Pass<'n, 'r> {
    numbering: &'n mut Numbering<'r>,
    /// Labels see the numbers below this one, those given before the pass began.
    frozen: usize,
    /// The label of each term labelled in this pass, by the address of its allocation.
    labels: FxHashMap<usize, u64>,
    stored_order: bool,
    /// The pending variables of the first group of tied elements the pass left.
    stuck: Option<Vec<Variable>>,
}

impl<'n, 'r> Pass<'n, 'r> {
    fn new(numbering: &'n mut Numbering<'r>, stored_order: bool) -> Self {
        let frozen = numbering.order.len();
        Self {
            numbering,
            frozen,
            labels: FxHashMap::default(),
            stored_order,
            stuck: None,
        }
    }

    fn object(&mut self, object: &Object<'_>) {
        for variable in object.variables {
            self.numbering.number(variable);
        }
        for term in object.terms {
            self.term(term);
        }
        self.predicates(object.predicates.iter());
    }

    /// The variables of `term` in preorder. The walk keeps an explicit stack, so a deep term
    /// does not deepen the call stack.
    fn term(&mut self, term: &Term) {
        let mut pending = vec![term];
        // Invariant: `pending` holds, last first, the subterms still to walk in preorder.
        while let Some(term) = pending.pop() {
            if !self.numbering.term_pending(term) {
                continue;
            }
            match term.kind() {
                TermKind::Variable(variable) => self.numbering.number(variable),
                TermKind::DomainValue { .. } => {}
                TermKind::And(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                TermKind::Application { arguments, .. } => pending.extend(arguments.iter().rev()),
                TermKind::Injection { term, .. } => pending.push(term),
                TermKind::Map { entries, rest, .. } => {
                    pending.extend(rest);
                    let entries = entries
                        .iter()
                        .filter(|(key, value)| {
                            self.numbering.term_pending(key) || self.numbering.term_pending(value)
                        })
                        .collect::<Vec<_>>();
                    let entries = self.order(
                        entries,
                        |pass, (key, value)| {
                            let labels = (pass.label(key), pass.label(value));
                            hash_of(&labels)
                        },
                        |numbering, (key, value), candidates| {
                            pending_of_term(numbering, key, candidates);
                            pending_of_term(numbering, value, candidates);
                        },
                    );
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
                    let elements = elements
                        .iter()
                        .filter(|element| self.numbering.term_pending(element))
                        .collect::<Vec<_>>();
                    let elements = self.order(elements, Self::label, pending_of_term);
                    pending.extend(elements.into_iter().rev());
                }
            }
        }
    }

    /// The operands of a conjunction or a disjunction (or the constraints) that hold a pending
    /// variable, walked in label order.
    fn predicates<'p>(&mut self, predicates: impl IntoIterator<Item = &'p Predicate>) {
        let predicates = predicates
            .into_iter()
            .filter(|predicate| self.numbering.predicate_pending(predicate))
            .collect::<Vec<_>>();
        for predicate in self.order(predicates, Self::predicate_label, pending_of_predicate) {
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
                self.numbering.number(binder);
                self.predicate(body);
            }
        }
    }

    /// `items`, unordered elements that each hold a pending variable, in the order to walk
    /// them: sorted by `label`; a group of two or more with one label is walked in stored
    /// order for the stored-order completion and left otherwise, its pending variables
    /// (`pending_of`) recorded when it is the first group left.
    fn order<'t, T: ?Sized>(
        &mut self,
        items: Vec<&'t T>,
        label: impl Fn(&mut Self, &T) -> u64,
        pending_of: impl Fn(&Numbering<'_>, &T, &mut BTreeSet<Variable>),
    ) -> Vec<&'t T> {
        if items.len() < 2 {
            return items;
        }
        let mut labelled = items
            .into_iter()
            .map(|item| (label(self, item), item))
            .collect::<Vec<_>>();
        // Stable, so a group keeps its stored order.
        labelled.sort_by_key(|(label, _)| *label);
        let mut ordered = Vec::with_capacity(labelled.len());
        for group in labelled.chunk_by(|left, right| left.0 == right.0) {
            if group.len() == 1 || self.stored_order {
                ordered.extend(group.iter().map(|(_, item)| *item));
            } else if self.stuck.is_none() {
                let mut candidates = BTreeSet::new();
                for (_, item) in group {
                    pending_of(self.numbering, item, &mut candidates);
                }
                self.stuck = Some(candidates.into_iter().collect());
            }
        }
        ordered
    }

    /// A hash of `term` that a renaming of the renamed variables among themselves does not
    /// change once it maps numbers to numbers: a renamed variable is labelled by its kind, its
    /// sort and its number if it had one when the pass began, every other node by its
    /// structure, the elements of a map or a set as a multiset. Labels equal for different
    /// terms only make the pass leave a group it could have ordered. Computed bottom-up with
    /// an explicit stack, once per allocation in a pass.
    fn label(&mut self, term: &Term) -> u64 {
        let mut stack = vec![(term, false)];
        // Invariant: a pair `(t, true)` sits below the pairs of all of `t`'s children.
        while let Some((node, children_labelled)) = stack.pop() {
            let address = address_of(node);
            if self.labels.contains_key(&address) {
                continue;
            }
            if !node
                .attributes()
                .variables
                .iter()
                .any(|variable| self.numbering.renamable.contains(variable))
            {
                // No renamed variable: the term itself, through its stored hash.
                self.labels.insert(address, hash_of(&(0u8, node)));
                continue;
            }
            if children_labelled {
                let label = self.node_label(node);
                self.labels.insert(address, label);
                continue;
            }
            stack.push((node, true));
            for_each_child(node, |child| stack.push((child, false)));
        }
        self.labels[&address_of(term)]
    }

    /// The label of `term` from the labels of its children.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn node_label(&self, term: &Term) -> u64 {
        let child = |child: &Term| self.labels[&address_of(child)];
        match term.kind() {
            TermKind::And(left, right) => hash_of(&(1u8, child(left), child(right))),
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } => hash_of(&(
                2u8,
                &symbol.name,
                sort_arguments,
                arguments.iter().map(child).collect::<Vec<_>>(),
            )),
            TermKind::DomainValue { .. } => hash_of(&(0u8, term)),
            TermKind::Variable(variable) => self.variable_label(variable),
            TermKind::Injection {
                source,
                target,
                term,
            } => hash_of(&(4u8, source, target, child(term))),
            TermKind::Map {
                definition,
                entries,
                rest,
            } => {
                let mut entries = entries
                    .iter()
                    .map(|(key, value)| hash_of(&(child(key), child(value))))
                    .collect::<Vec<_>>();
                entries.sort_unstable();
                hash_of(&(5u8, definition, entries, rest.as_ref().map(child)))
            }
            TermKind::List {
                definition,
                heads,
                rest,
            } => hash_of(&(
                6u8,
                definition,
                heads.iter().map(child).collect::<Vec<_>>(),
                rest.as_ref().map(|(middle, tails)| {
                    (child(middle), tails.iter().map(child).collect::<Vec<_>>())
                }),
            )),
            TermKind::Set {
                definition,
                elements,
                rest,
            } => {
                let mut elements = elements.iter().map(child).collect::<Vec<_>>();
                elements.sort_unstable();
                hash_of(&(7u8, definition, elements, rest.as_ref().map(child)))
            }
        }
    }

    fn variable_label(&self, variable: &Variable) -> u64 {
        if self.numbering.renamable.contains(variable) {
            let number = self
                .numbering
                .index
                .get(variable)
                .filter(|number| **number < self.frozen);
            hash_of(&(3u8, variable.kind, &variable.sort, number))
        } else {
            hash_of(&(8u8, variable))
        }
    }

    /// [`Pass::label`] for a predicate, the operands of a conjunction or a disjunction as a
    /// multiset.
    #[deny(clippy::wildcard_enum_match_arm)]
    fn predicate_label(&mut self, predicate: &Predicate) -> u64 {
        match predicate {
            Predicate::True => hash_of(&10u8),
            Predicate::False => hash_of(&11u8),
            Predicate::Term(term) => hash_of(&(12u8, self.label(term))),
            Predicate::Equals(left, right) => hash_of(&(13u8, self.label(left), self.label(right))),
            Predicate::Ceil(term) => hash_of(&(14u8, self.label(term))),
            Predicate::Floor(term) => hash_of(&(15u8, self.label(term))),
            Predicate::In(left, right) => hash_of(&(16u8, self.label(left), self.label(right))),
            Predicate::Not(inner) => hash_of(&(17u8, self.predicate_label(inner))),
            Predicate::And(operands) | Predicate::Or(operands) => {
                let tag = if matches!(predicate, Predicate::And(_)) {
                    18u8
                } else {
                    19
                };
                let mut operands = operands
                    .iter()
                    .map(|operand| self.predicate_label(operand))
                    .collect::<Vec<_>>();
                operands.sort_unstable();
                hash_of(&(tag, operands))
            }
            Predicate::Implies(left, right) => hash_of(&(
                20u8,
                self.predicate_label(left),
                self.predicate_label(right),
            )),
            Predicate::Iff(left, right) => hash_of(&(
                21u8,
                self.predicate_label(left),
                self.predicate_label(right),
            )),
            Predicate::Exists(binder, body) => hash_of(&(
                22u8,
                self.variable_label(binder),
                self.predicate_label(body),
            )),
            Predicate::Forall(binder, body) => hash_of(&(
                23u8,
                self.variable_label(binder),
                self.predicate_label(body),
            )),
        }
    }
}

/// Add the pending variables of `term` to `candidates`.
fn pending_of_term(numbering: &Numbering<'_>, term: &Term, candidates: &mut BTreeSet<Variable>) {
    candidates.extend(
        term.attributes()
            .variables
            .iter()
            .filter(|variable| numbering.pending(variable))
            .cloned(),
    );
}

/// Add the pending variables of `predicate`, free or bound, to `candidates`.
fn pending_of_predicate(
    numbering: &Numbering<'_>,
    predicate: &Predicate,
    candidates: &mut BTreeSet<Variable>,
) {
    let mut variables = BTreeSet::new();
    collect_all_variables(std::iter::once(predicate), &mut variables);
    candidates.extend(
        variables
            .into_iter()
            .filter(|variable| numbering.pending(variable)),
    );
}

/// The address of `term`'s allocation, which identifies it while it is alive.
fn address_of(term: &Term) -> usize {
    std::ptr::from_ref(term.kind()) as usize
}

fn hash_of(value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[deny(clippy::wildcard_enum_match_arm)]
fn for_each_child<'t>(term: &'t Term, mut visit: impl FnMut(&'t Term)) {
    match term.kind() {
        TermKind::Variable(_) | TermKind::DomainValue { .. } => {}
        TermKind::And(left, right) => {
            visit(left);
            visit(right);
        }
        TermKind::Application { arguments, .. } => arguments.iter().for_each(visit),
        TermKind::Injection { term, .. } => visit(term),
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                visit(key);
                visit(value);
            }
            rest.iter().for_each(visit);
        }
        TermKind::List { heads, rest, .. } => {
            heads.iter().for_each(&mut visit);
            if let Some((middle, tails)) = rest {
                visit(middle);
                tails.iter().for_each(visit);
            }
        }
        TermKind::Set { elements, rest, .. } => {
            elements.iter().for_each(&mut visit);
            rest.iter().for_each(visit);
        }
    }
}

/// The renaming [`RequestNames::canonical`] chose.
#[derive(Default)]
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
        conjunction_set(if self.renaming.is_empty() {
            predicates.to_vec()
        } else {
            rename_predicates(predicates, |variable| self.variable(variable))
        })
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
        term::{CollectionSymbols, ListDefinition, MapDefinition, Sort, Symbol},
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

    /// `go(map, list)`: a map from element variables named by `keys` to `0`, and the list of
    /// the element variables named by `list`, the shape a rule `go(M, L) => go(M (?K |-> 0), L
    /// ListItem(?K))` builds.
    fn map_and_list(keys: &[&str], list: &[&str]) -> Pattern {
        let entries = keys.iter().map(|key| (*key, "0")).collect::<Vec<_>>();
        let list_definition = Arc::new(ListDefinition {
            symbols: CollectionSymbols {
                unit: "listUnit".into(),
                element: "listElement".into(),
                concat: "listConcat".into(),
            },
            element_sort: "SortS".into(),
            list_sort: "SortList".into(),
        });
        let list = Term::list(
            list_definition,
            list.iter()
                .map(|name| Term::variable(variable(name)))
                .collect(),
            None,
        );
        Pattern {
            term: go(vec![map(&entries), list]),
            constraints: Vec::new(),
        }
    }

    /// `go(arguments)`, a constructor application.
    fn go(arguments: Vec<Term>) -> Term {
        let symbol = Arc::new(Symbol::constructor(
            "go",
            arguments.iter().map(Term::sort).collect(),
            Sort::simple("SortS"),
        ));
        Term::application(symbol, Vec::new(), arguments)
    }

    /// Map entries that differ only in the names of their keys tie, and their stored order
    /// compares names (`!10` before `!3`); the list tells them apart, so two renamings of
    /// one state get one key whatever order their names store the entries in.
    #[test]
    fn a_state_key_orders_tied_map_entries_by_where_their_variables_occur_elsewhere() {
        let request = RequestNames::default();
        let first = map_and_list(
            &["Ex#K!0", "Ex#K!3", "Ex#K!6", "Ex#K!9"],
            &["Ex#K!0", "Ex#K!3", "Ex#K!6", "Ex#K!9"],
        );
        let second = map_and_list(
            &["Ex#K!0", "Ex#K!10", "Ex#K!3", "Ex#K!6"],
            &["Ex#K!0", "Ex#K!3", "Ex#K!6", "Ex#K!10"],
        );
        assert_eq!(request.state_key(&first), request.state_key(&second));
        let reordered = map_and_list(
            &["Ex#K!0", "Ex#K!3", "Ex#K!6", "Ex#K!9"],
            &["Ex#K!9", "Ex#K!0", "Ex#K!3", "Ex#K!6"],
        );
        assert_eq!(
            request.state_key(&first),
            request.state_key(&reordered),
            "a permutation of the list is a renaming of the map's keys"
        );
        let repeated = map_and_list(
            &["Ex#K!0", "Ex#K!3", "Ex#K!6", "Ex#K!9"],
            &["Ex#K!0", "Ex#K!0", "Ex#K!6", "Ex#K!9"],
        );
        assert_ne!(request.state_key(&first), request.state_key(&repeated));
    }

    /// The map `{key |-> value}` over element variables of sort `SortS` on both sides.
    fn variable_map(entries: &[(&str, &str)]) -> Pattern {
        let definition = Arc::new(MapDefinition {
            symbols: CollectionSymbols {
                unit: "unit".into(),
                element: "element".into(),
                concat: "concat".into(),
            },
            key_sort: "SortS".into(),
            value_sort: "SortS".into(),
            map_sort: "SortMap".into(),
        });
        Pattern {
            term: Term::map(
                definition,
                entries
                    .iter()
                    .map(|(key, value)| {
                        (
                            Term::variable(variable(key)),
                            Term::variable(variable(value)),
                        )
                    })
                    .collect(),
                None,
            ),
            constraints: Vec::new(),
        }
    }

    /// `{X |-> Y, Y |-> Y}`: the two entries tie while neither variable has a number, and
    /// nothing outside the map tells them apart, so a numbering must start from one of the
    /// variables. Stored order starts from whichever name sorts first, which a renaming
    /// changes; the key is the least over both starts, so it does not.
    #[test]
    fn a_state_key_tries_each_variable_of_a_group_nothing_orders() {
        let request = RequestNames::default();
        let key = |entries: &[(&str, &str)]| request.state_key(&variable_map(entries));
        let first = key(&[("Ex#A!0", "Ex#B!1"), ("Ex#B!1", "Ex#B!1")]);
        let second = key(&[("Ex#B!1", "Ex#A!0"), ("Ex#A!0", "Ex#A!0")]);
        assert_eq!(first, second);
        assert_ne!(
            first,
            key(&[("Ex#A!0", "Ex#A!0"), ("Ex#B!1", "Ex#B!1")]),
            "two loops are not a loop and an edge into it"
        );
        let cycle = key(&[
            ("Ex#A!0", "Ex#B!1"),
            ("Ex#B!1", "Ex#C!2"),
            ("Ex#C!2", "Ex#A!0"),
        ]);
        assert_eq!(
            cycle,
            key(&[
                ("Ex#A!0", "Ex#C!2"),
                ("Ex#C!2", "Ex#B!1"),
                ("Ex#B!1", "Ex#A!0"),
            ])
        );
    }

    /// The set of `names` as element variables of sort `SortS`.
    fn variable_set(names: &[String]) -> Term {
        let definition = Arc::new(ListDefinition {
            symbols: CollectionSymbols {
                unit: "setUnit".into(),
                element: "setElement".into(),
                concat: "setConcat".into(),
            },
            element_sort: "SortS".into(),
            list_sort: "SortSet".into(),
        });
        Term::set(
            definition,
            names
                .iter()
                .map(|name| Term::variable(variable(name)))
                .collect(),
            None,
        )
    }

    /// Variables that every exchange maps the state to itself are tried once: the 40 elements
    /// of the set are one class, so the search numbers them along one path and still has
    /// budget for the two starts the map `{X |-> Y, Y |-> Y}` needs, where trying every
    /// element would exhaust it and fall back to stored order, which depends on the names
    /// of `X` and `Y`. A few kilobytes, well under a second.
    #[test]
    fn a_state_key_tries_interchangeable_variables_once() {
        let request = RequestNames::default();
        let key = |offset: usize, x: &str, y: &str| {
            let set = (0..40)
                .map(|index| format!("Ex#K!{}", index + offset))
                .collect::<Vec<_>>();
            let map = variable_map(&[(x, y), (y, y)]).term;
            request.state_key(&Pattern {
                term: go(vec![variable_set(&set), map]),
                constraints: Vec::new(),
            })
        };
        assert_eq!(key(0, "Ex#A!0", "Ex#B!1"), key(95, "Ex#B!1", "Ex#A!0"),);
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
