//! The dictionary proposer: guard harvesting (ARCHITECTURE 8.3). Owner: FZ-11.
//!
//! # Why harvesting works
//!
//! A rule applies only where its left-hand side matches and its `requires` holds, and a guard
//! that compares a hole's value with a constant (`C ==Int 7`, `S ==String "open"`) holds on a
//! set of values a blind draw almost never hits. The constant is written in the definition, so
//! the proposer reads it there instead of guessing it: a literal of a guard is a value that
//! passes or bounds an equality, and a literal plus or minus a little is a value on either side
//! of a strict comparison's boundary (`1000 < D < 1100` holds for `1000 + 1`).
//!
//! # The static harvest
//!
//! [`Harvest::from_graph`] reads the literals (domain values of every sort) and the constant
//! constructors (free constructors of arity 0) of these terms:
//!
//! - the left-hand side and the `requires` of every rewrite rule whose least distance to the
//!   target in the rule graph is at most [`RADIUS`] edges (ARCHITECTURE 6.3: an edge from A to
//!   B when a step of A may enable B, so these are the rules a path to the target takes last;
//!   the target itself is at distance 0);
//! - the left-hand side, the `requires` and the conditions written in the right-hand side of
//!   every equation of the functions those `requires` apply, transitively through the functions
//!   the equations apply ([`RuleGraph::requires_functions`]): a guard such as
//!   `limit(N) ==Int 1` holds or fails by the conditions of `limit`'s equations, which are
//!   guards on `N` too. A condition in a right-hand side is a `Bool` subterm there: the whole
//!   right-hand side of a Boolean helper (`good(N) => N ==Int 4711`), or the condition of an
//!   `#if` (`pick(N) => #if N ==Int 31337 #then 1 #else 0 #fi`); the values an equation returns
//!   (the branches, `limit`'s `0`) are no conditions;
//! - for a rule in that set that some higher-priority rule may compete with (an `owise` rule,
//!   or one with a larger explicit priority), the left-hand side and `requires` of those
//!   competitors and of the equations their `requires` apply. A lower-priority rule applies
//!   only where every competitor that matches fails its guard, so the competitors' guards are
//!   its own implicit guard, negated. Two rules may compete when their roots may be equal and
//!   each cell key covers the other's (the keys the backend selects rules by).
//!
//! A target that is not a rule has no place in the graph ([`harvest`]). A pattern target's own
//! body and `requires` are its left-hand side and guard, harvested at distance 0 with the
//! equations they call, and every rewrite rule at distance 1. A differential target is decided
//! where the two definitions differ: the rules and equations of either definition whose ids the
//! other lacks are harvested at distance 0, and every baseline rule at distance 1. An observer
//! target states no guard, so every rewrite rule counts at distance 0.
//!
//! Each literal keeps the least distance it was harvested at. The graph only over-approximates
//! enablement and the harvest reads guards it cannot evaluate, so a harvested value is a
//! guess, never evidence: it becomes a case like any other.
//!
//! # From literals to hole values
//!
//! [`HolePool::new`] turns the harvest into the values one hole may take. A literal applies to
//! a hole when it is a domain value of the hole's KORE sort (`SortInt` for an `Int` hole, the
//! renamed sort for a renamed builtin, `SortMInt{Sort8{}}` for `MInt{8}`), or, for a data
//! hole, a constant constructor or a builtin literal that is a value of the hole's sort. Each
//! applicable literal is a *base*; an integer base also yields the variants `v - 3` .. `v + 3`
//! and `-v` (for `MInt`, the variants inside `0 .. 2^width` and the two's-complement negation),
//! and a `Bool` base its negation. Every base and variant must pass the hole's sort, its
//! constraints ([`values::check_constraints`]) and the generator's size rules (the integer bit
//! bound of [`GenerationBounds`], the length bound, a data term's depth bound, and so
//! [`values::MAX_VALUE_SIZE`]); one that does not is dropped. Collection holes take no
//! harvested values. A case built from these values still goes through the per-case
//! round-trip check and is `rejected` when the program's grammar refuses it.
//!
//! # Drawing
//!
//! For each hole whose pool is not empty, the proposer draws from the pool with the fixed
//! probability [`DRAW_PROBABILITY`], and otherwise from the hole's generator, as blind sampling
//! does. A pool draw picks a base with weight `4^(RADIUS - distance)`, then the base itself
//! with probability 1/2 and otherwise one of its variants uniformly. A constant of the target's
//! own guard thus weighs four times one a step before and sixteen times one two steps before.
//! The steep weights are deliberate: a constant of the target's own guard surely concerns the
//! target, while the rule graph's distances are coarse (a rule that ends with a bare
//! continuation is one edge before every rule), so the constants one or two edges away are
//! many, and each concerns the target only when the path passes its rule.
//!
//! Every choice is drawn from a `ChaCha20` stream and a proptest runner seeded from the campaign
//! seed under purposes of their own (`dictionary`, `dictionary-values`), so the dictionary's
//! draws never shift the schedule's or blind sampling's streams.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust::{
    k_rust_backend::{
        rule::{IndexedRewriteRule, RewriteRule, RuleRhs, TermIndex, term_index},
        term::{HeadRole, Sort, SortNode, Term, TermKind},
    },
    kore::{
        ast::{Pattern as KorePattern, Sort as KoreSort},
        walk,
    },
};
use num_bigint::{BigInt, BigUint};
use num_traits::Signed as _;
use rand::{Rng as _, SeedableRng as _};
use rand_chacha::ChaCha20Rng;

use crate::{
    assemble::{ProgramAssembly, build_backend},
    engine::proposer::{Observation, Origin, Proposal, ProposalContext, Proposer, ValueShrinker},
    error::{CampaignError, TargetProblem},
    exec::run::PatternCompiler,
    graph::RuleGraph,
    holes::ResolvedHole,
    report::DictionaryParameters,
    spec::{CampaignSpec, ProposerKind},
    target::{TargetKind, resolve_rule},
    values::{self, Constraints, GenerationBounds, Generator, Value, ValueRng, ValueSort},
};

/// The harvest radius: rules at most this many rule-graph edges before the target
/// (ARCHITECTURE 6.3, 8.3).
///
/// Two edges reach the guards of the step that enables the target and of the step before it,
/// which is what a nested guard needs (the stall benchmark's `c5` needs `c3`'s and `c4`'s
/// constants). On definitions whose rules end with a bare continuation (`=> .K ...`), which
/// enables every rule, most rules are within one or two edges anyway (FZ-G8 review), so a
/// larger radius would add little but dilution.
pub(crate) const RADIUS: usize = 2;

/// The probability with which a hole with a non-empty pool takes a harvested value in a
/// dictionary proposal, as (numerator, denominator); otherwise it is drawn blindly.
///
/// One half keeps the holes that no harvested constant concerns (the dictionary cannot tell
/// which hole a guard reads without the matched substitutions, G-7) as varied as blind
/// sampling half of the time, while a hole whose guard needs a constant gets one every other
/// proposal.
pub(crate) const DRAW_PROBABILITY: (u32, u32) = (1, 2);

/// The largest offset of an integer variant: a base `v` yields `v - 3` .. `v + 3`.
pub(crate) const EXPANSION: u8 = 3;

/// A harvested constant's weight is `DISTANCE_WEIGHT_BASE ^ (RADIUS - distance)` (module
/// documentation, "Drawing").
pub(crate) const DISTANCE_WEIGHT_BASE: u64 = 4;

/// The probability, as (numerator, denominator), with which a pool draw takes the harvested
/// constant itself rather than one of its variants.
pub(crate) const EXACT_PROBABILITY: (u32, u32) = (1, 2);

/// The KORE sort of `Bool`, as [`sort_text`] writes it.
const BOOL_SORT: &str = "SortBool{}";

/// The dictionary's parameters as the report records them ([`DictionaryParameters`]).
pub(crate) fn parameters() -> DictionaryParameters {
    DictionaryParameters {
        radius: u32::try_from(RADIUS).unwrap_or(u32::MAX),
        draw_probability: [DRAW_PROBABILITY.0, DRAW_PROBABILITY.1],
        expansion: u32::from(EXPANSION),
        distance_weight_base: u32::try_from(DISTANCE_WEIGHT_BASE).unwrap_or(u32::MAX),
        exact_probability: [EXACT_PROBABILITY.0, EXACT_PROBABILITY.1],
    }
}

/// The harvest of a campaign on `spec` whose baseline's rule graph is `graph` and whose rule
/// target, if any, has the catalog id `target` (module documentation, "The static harvest"):
///
/// - a rule target: [`Harvest::from_graph`] within [`RADIUS`];
/// - a pattern target: the pattern's own body and `requires`, and the equations they call, at
///   distance 0, and every rule at distance 1;
/// - a differential target: [`Harvest::differential`], on the mutant's graph built here (an
///   internalization of the mutant of its own);
/// - an observer target, which states no guard: every rule at distance 0.
///
/// # Errors
///
/// [`CampaignError`] when the program grammar, the pattern compiler or the mutant's backend
/// does not build; `Campaign::new` has built each of them once already.
pub(crate) fn harvest(
    spec: &CampaignSpec,
    graph: &RuleGraph,
    target: Option<&str>,
) -> Result<Harvest, CampaignError> {
    Ok(match &spec.target.kind {
        TargetKind::Rule(_) => Harvest::from_graph(graph, target, RADIUS),
        TargetKind::Pattern(pattern) => {
            let baseline = &spec.definitions.baseline;
            let assembly = ProgramAssembly::new(baseline)?;
            let compiled = PatternCompiler::new(baseline)?
                .compile(assembly.grammar(), &pattern.pattern)
                .map_err(|message| CampaignError::Target(TargetProblem::Pattern(message)))?;
            let mut harvest = Harvest::everything(graph, 1);
            harvest.pattern(compiled.kore(), graph);
            harvest
        }
        TargetKind::Differential(_) => match &spec.definitions.mutant {
            Some(mutant) => {
                let mut backend = build_backend(mutant, spec.options.backend.options())?;
                let mutant = RuleGraph::of_backend(&mut backend).map_err(|error| {
                    CampaignError::Definition {
                        message: format!("the mutant's rule graph is not available: {error}"),
                    }
                })?;
                Harvest::differential(graph, &mutant)
            }
            None => Harvest::everything(graph, 0),
        },
        TargetKind::Observer(_) => Harvest::everything(graph, 0),
    })
}

/// A literal of a guard or a left-hand side, independent of any backend term.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum Literal {
    /// A domain value: its KORE sort, written as KORE writes it (`SortInt`,
    /// `SortMInt{Sort8{}}`), and its bytes.
    Domain {
        /// The KORE sort.
        sort: String,
        /// The domain value's bytes.
        text: Vec<u8>,
    },
    /// A free constructor of arity 0, by KORE symbol name.
    Constant {
        /// The symbol.
        symbol: String,
    },
}

/// The literals the static pass harvested, each with the least rule-graph distance to the
/// target it was harvested at (module documentation, "The static harvest").
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Harvest {
    literals: BTreeMap<Literal, usize>,
}

impl Harvest {
    /// Harvest the literals for a campaign on `spec`: on a backend of the baseline of its own
    /// (no case runs on it), resolve a rule target's id in the rule catalog, build the rule
    /// graph and harvest within [`RADIUS`].
    ///
    /// # Errors
    ///
    /// [`CampaignError::Definition`] when the backend, its catalog or its graph is not
    /// available, and [`CampaignError::Target`] for a rule reference the catalog does not
    /// resolve; `Campaign::new` refuses both earlier, when it resolves the target.
    pub(crate) fn for_campaign(spec: &CampaignSpec) -> Result<Self, CampaignError> {
        let mut backend =
            build_backend(&spec.definitions.baseline, spec.options.backend.options())?;
        let target = match &spec.target.kind {
            TargetKind::Rule(rule) => {
                let catalog =
                    backend
                        .rule_catalog(None)
                        .map_err(|error| CampaignError::Definition {
                            message: format!("the rule catalog is not available: {error}"),
                        })?;
                Some(resolve_rule(&catalog, &rule.rule).map_err(CampaignError::Target)?)
            }
            TargetKind::Pattern(_) | TargetKind::Differential(_) | TargetKind::Observer(_) => None,
        };
        let graph =
            RuleGraph::of_backend(&mut backend).map_err(|error| CampaignError::Definition {
                message: format!("the rule graph is not available: {error}"),
            })?;
        harvest(spec, &graph, target.as_deref())
    }

    /// Harvest from `graph`'s rules within `radius` edges before `target`, or from every rule
    /// when `target` is `None` (module documentation, "The static harvest"). A `target` that is
    /// no node of the graph harvests nothing.
    pub(crate) fn from_graph(graph: &RuleGraph, target: Option<&str>, radius: usize) -> Self {
        match target {
            Some(target) => {
                let scope = graph
                    .distances_to(target)
                    .into_iter()
                    .filter(|(_, distance)| *distance <= radius)
                    .collect();
                Self::from_scope(graph, &scope, true)
            }
            None => Self::everything(graph, 0),
        }
    }

    /// Harvest every rule of `graph` (and the equations their `requires` call) at `distance`.
    fn everything(graph: &RuleGraph, distance: usize) -> Self {
        let scope = graph
            .rule_ids()
            .map(|id| (id.to_owned(), distance))
            .collect();
        // Every rule is in scope, so every competitor already is.
        Self::from_scope(graph, &scope, false)
    }

    /// Harvest the rules of `scope` at their distances, with the equations their `requires`
    /// call, and with their competitors when `competitors` is set.
    fn from_scope(graph: &RuleGraph, scope: &BTreeMap<String, usize>, competitors: bool) -> Self {
        let all: Vec<Keyed<'_>> = if competitors {
            graph
                .rule_ids()
                .flat_map(|id| graph.rules(id).iter().map(move |rule| Keyed::new(id, rule)))
                .collect()
        } else {
            Vec::new()
        };
        let mut harvest = Self::default();
        for (id, &distance) in scope {
            let mut guards: BTreeSet<&str> = BTreeSet::from([id.as_str()]);
            for rule in graph.rules(id) {
                harvest.rule(rule, distance);
                let rule = Keyed::new(id, rule);
                for competitor in all.iter().filter(|competitor| competitor.competes(&rule)) {
                    harvest.rule(competitor.rule, distance);
                    guards.insert(competitor.id);
                }
            }
            for guard in guards {
                harvest.called(graph, graph.requires_functions(guard), distance);
            }
        }
        harvest
    }

    /// Harvest the equations of `functions` (a call closure) at `distance`.
    fn called(&mut self, graph: &RuleGraph, functions: BTreeSet<String>, distance: usize) {
        for function in functions {
            for equation in graph.calls().equations(&function) {
                self.equation(equation, distance);
            }
        }
    }

    /// The harvest of a differential campaign (ARCHITECTURE 4.3): the rules and equations of
    /// either definition whose ids the other lacks at distance 0 (an edited, added or removed
    /// axiom, which is where the two definitions differ and so where a killing input is decided),
    /// with the equations their `requires` call; and every rule of the baseline at distance 1.
    pub(crate) fn differential(baseline: &RuleGraph, mutant: &RuleGraph) -> Self {
        let mut harvest = Self::everything(baseline, 1);
        harvest.differing(baseline, mutant);
        harvest.differing(mutant, baseline);
        harvest
    }

    /// Harvest at distance 0 the rules and equations of `side` whose ids `other` lacks.
    fn differing(&mut self, side: &RuleGraph, other: &RuleGraph) {
        let known: BTreeSet<&str> = other
            .rule_ids()
            .chain(
                other
                    .calls()
                    .all_equations()
                    .map(|equation| equation.attributes.unique_id.as_str()),
            )
            .collect();
        for id in side.rule_ids().filter(|id| !known.contains(id)) {
            for rule in side.rules(id) {
                self.rule(rule, 0);
            }
            self.called(side, side.requires_functions(id), 0);
        }
        for equation in side.calls().all_equations() {
            if !known.contains(equation.attributes.unique_id.as_str()) {
                self.equation(equation, 0);
            }
        }
    }

    /// Harvest a pattern target's compiled KORE pattern at distance 0: its body and its
    /// `requires` are the target's left-hand side and guard (ARCHITECTURE 4.1), with the
    /// equations of the functions it applies.
    fn pattern(&mut self, pattern: &KorePattern, graph: &RuleGraph) {
        let mut symbols = BTreeSet::new();
        walk::for_each_post_order(pattern, |node| match node {
            KorePattern::DomainValue { sort, value } => {
                if let Some(sort) = kore_sort_text(sort) {
                    self.insert(
                        Literal::Domain {
                            sort,
                            text: value.as_bytes().to_vec(),
                        },
                        0,
                    );
                }
            }
            KorePattern::Application { symbol, arguments } => {
                if arguments.is_empty() {
                    self.insert(
                        Literal::Constant {
                            symbol: symbol.name.clone(),
                        },
                        0,
                    );
                }
                symbols.insert(symbol.name.clone());
            }
            _ => {}
        });
        self.called(graph, graph.calls().closure(symbols), 0);
    }

    /// A harvest of the given literals and distances.
    #[cfg(test)]
    pub(crate) fn from_literals(literals: BTreeMap<Literal, usize>) -> Self {
        Self { literals }
    }

    /// The harvested literals and their least distances.
    pub(crate) fn literals(&self) -> &BTreeMap<Literal, usize> {
        &self.literals
    }

    /// Harvest an equation at `distance`: its left-hand side and `requires`, and the
    /// conditions written in its right-hand side: every `Bool` subterm, which is the whole
    /// right-hand side of a Boolean helper (`good(N) => N ==Int 4711`) and the condition of an
    /// `#if` (`KEQUAL.ite`), but not the values an equation returns.
    fn equation(&mut self, equation: &RewriteRule, distance: usize) {
        self.rule(equation, distance);
        let mut visit = |term: &Term| self.conditions(term, distance);
        match &equation.rhs {
            RuleRhs::Term(term) => visit(term),
            RuleRhs::Disjunction(alternatives) => {
                for alternative in alternatives {
                    visit(&alternative.term);
                }
            }
            RuleRhs::Predicates(predicates) => {
                for predicate in predicates {
                    predicate.visit_terms(&mut visit);
                }
            }
            RuleRhs::Top | RuleRhs::Bottom => {}
        }
    }

    /// Harvest the `Bool` subterms of `term` at `distance`.
    fn conditions(&mut self, term: &Term, distance: usize) {
        if sort_text(term.sort()).as_deref() == Some(BOOL_SORT) {
            self.term(term, distance);
            return;
        }
        match term.kind() {
            TermKind::Application { arguments, .. } => {
                for argument in arguments {
                    self.conditions(argument, distance);
                }
            }
            TermKind::And(left, right) => {
                self.conditions(left, distance);
                self.conditions(right, distance);
            }
            TermKind::Injection { term, .. } => self.conditions(term, distance),
            TermKind::Map { entries, rest, .. } => {
                for (key, value) in entries {
                    self.conditions(key, distance);
                    self.conditions(value, distance);
                }
                if let Some(rest) = rest {
                    self.conditions(rest, distance);
                }
            }
            TermKind::List { heads, rest, .. } => {
                for head in heads {
                    self.conditions(head, distance);
                }
                if let Some((middle, tails)) = rest {
                    self.conditions(middle, distance);
                    for tail in tails {
                        self.conditions(tail, distance);
                    }
                }
            }
            TermKind::Set { elements, rest, .. } => {
                for element in elements {
                    self.conditions(element, distance);
                }
                if let Some(rest) = rest {
                    self.conditions(rest, distance);
                }
            }
            TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        }
    }

    /// Harvest `rule`'s left-hand side and `requires` at `distance`.
    fn rule(&mut self, rule: &RewriteRule, distance: usize) {
        let mut visit = |term: &Term| self.term(term, distance);
        visit(&rule.lhs);
        for predicate in rule.requires.iter() {
            predicate.visit_terms(&mut visit);
        }
    }

    fn term(&mut self, term: &Term, distance: usize) {
        match term.kind() {
            TermKind::DomainValue { sort, value } => {
                if let Some(sort) = sort_text(*sort) {
                    self.insert(
                        Literal::Domain {
                            sort,
                            text: value.as_bytes().to_vec(),
                        },
                        distance,
                    );
                }
            }
            TermKind::Application {
                symbol, arguments, ..
            } => {
                if arguments.is_empty()
                    && symbol.attributes.head_role() == HeadRole::FreeConstructor
                {
                    self.insert(
                        Literal::Constant {
                            symbol: symbol.name.to_string(),
                        },
                        distance,
                    );
                }
                for argument in arguments {
                    self.term(argument, distance);
                }
            }
            TermKind::And(left, right) => {
                self.term(left, distance);
                self.term(right, distance);
            }
            TermKind::Injection { term, .. } => self.term(term, distance),
            TermKind::Map { entries, rest, .. } => {
                for (key, value) in entries {
                    self.term(key, distance);
                    self.term(value, distance);
                }
                if let Some(rest) = rest {
                    self.term(rest, distance);
                }
            }
            TermKind::List { heads, rest, .. } => {
                for head in heads {
                    self.term(head, distance);
                }
                if let Some((middle, tails)) = rest {
                    self.term(middle, distance);
                    for tail in tails {
                        self.term(tail, distance);
                    }
                }
            }
            TermKind::Set { elements, rest, .. } => {
                for element in elements {
                    self.term(element, distance);
                }
                if let Some(rest) = rest {
                    self.term(rest, distance);
                }
            }
            TermKind::Variable(_) => {}
        }
    }

    fn insert(&mut self, literal: Literal, distance: usize) {
        self.literals
            .entry(literal)
            .and_modify(|least| *least = (*least).min(distance))
            .or_insert(distance);
    }
}

/// A rewrite rule with its id and its left-hand side's root bucket.
struct Keyed<'g> {
    id: &'g str,
    rule: &'g IndexedRewriteRule,
    root: TermIndex,
}

impl<'g> Keyed<'g> {
    fn new(id: &'g str, rule: &'g IndexedRewriteRule) -> Self {
        Self {
            id,
            rule,
            root: term_index(&rule.lhs),
        }
    }

    /// Whether this rule has a higher priority than `rule` (a smaller priority number) and may
    /// match a configuration `rule` matches: their left-hand sides' roots may be equal (two
    /// distinct symbols never are) and, at each cell position, one of the two keys covers the
    /// other.
    fn competes(&self, rule: &Keyed<'_>) -> bool {
        if self.rule.attributes.priority >= rule.rule.attributes.priority {
            return false;
        }
        let roots = match (&self.root, &rule.root) {
            (TermIndex::Symbol(left), TermIndex::Symbol(right)) => left == right,
            _ => true,
        };
        let (left, right) = (self.rule.index.cells(), rule.rule.index.cells());
        roots
            && left.len() == right.len()
            && left
                .iter()
                .zip(right)
                .all(|(left, right)| left.covers(right) || right.covers(left))
    }
}

/// A backend sort as KORE writes it; `None` for a sort variable.
fn sort_text(sort: Sort) -> Option<String> {
    match sort.node() {
        SortNode::Application { name, arguments } => {
            let arguments = arguments
                .iter()
                .copied()
                .map(sort_text)
                .collect::<Option<Vec<String>>>()?;
            Some(format!("{name}{{{}}}", arguments.join(",")))
        }
        SortNode::Variable(_) => None,
    }
}

/// A KORE sort as [`sort_text`] writes a backend sort; `None` for a sort variable.
fn kore_sort_text(sort: &KoreSort) -> Option<String> {
    match sort {
        KoreSort::Application { name, arguments } => {
            let arguments = arguments
                .iter()
                .map(kore_sort_text)
                .collect::<Option<Vec<String>>>()?;
            Some(format!("{name}{{{}}}", arguments.join(",")))
        }
        KoreSort::Variable(_) => None,
    }
}

/// One harvested value of a hole and its variants, all admissible.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Base {
    /// `4^(RADIUS - distance)`.
    weight: u64,
    /// The literal itself, when it is admissible.
    exact: Option<Value>,
    /// Its admissible variants other than itself.
    variants: Vec<Value>,
}

/// The values one hole may take from the harvest (module documentation, "From literals to hole
/// values").
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct HolePool {
    bases: Vec<Base>,
    total: u64,
}

impl HolePool {
    /// The pool of a hole of `sort` under `constraints` and `bounds`.
    pub(crate) fn new(
        harvest: &Harvest,
        sort: &ValueSort,
        constraints: &Constraints,
        bounds: &GenerationBounds,
    ) -> Self {
        let own_sort = match sort.generated() {
            ValueSort::Int
            | ValueSort::Bool
            | ValueSort::String
            | ValueSort::Bytes
            | ValueSort::MInt { .. }
            | ValueSort::Token { .. } => sort.kore_sort().ok().as_ref().and_then(kore_sort_text),
            _ => None,
        };
        let mut weights: BTreeMap<Value, u64> = BTreeMap::new();
        for (literal, distance) in harvest.literals() {
            let Some(value) = literal_value(literal, sort, own_sort.as_deref()) else {
                continue;
            };
            let exponent = u32::try_from(RADIUS.saturating_sub(*distance)).unwrap_or(u32::MAX);
            let weight = DISTANCE_WEIGHT_BASE
                .checked_pow(exponent)
                .unwrap_or(u64::MAX >> 8);
            weights
                .entry(value)
                .and_modify(|known| *known = (*known).max(weight))
                .or_insert(weight);
        }
        let admits = |value: &Value| values::admissible(value, sort, constraints, bounds);
        let mut bases = Vec::new();
        for (value, weight) in weights {
            let variants: Vec<Value> = variants(&value)
                .into_iter()
                .filter(|variant| *variant != value && admits(variant))
                .collect::<BTreeSet<Value>>()
                .into_iter()
                .collect();
            let exact = admits(&value).then_some(value);
            if exact.is_some() || !variants.is_empty() {
                bases.push(Base {
                    weight,
                    exact,
                    variants,
                });
            }
        }
        let total = bases.iter().map(|base| base.weight).sum();
        Self { bases, total }
    }

    /// Whether the pool has no value.
    pub(crate) fn is_empty(&self) -> bool {
        self.bases.is_empty()
    }

    /// Every value the pool may give, in order, without repetition.
    #[cfg(test)]
    pub(crate) fn values(&self) -> BTreeSet<Value> {
        self.bases
            .iter()
            .flat_map(|base| base.exact.iter().chain(&base.variants))
            .cloned()
            .collect()
    }

    /// The harvested values themselves (the bases that are admissible), with their weights.
    #[cfg(test)]
    pub(crate) fn exact(&self) -> BTreeMap<Value, u64> {
        self.bases
            .iter()
            .filter_map(|base| base.exact.clone().map(|value| (value, base.weight)))
            .collect()
    }

    /// One draw: a base by weight, then the base itself with probability 1/2 (or always, when
    /// it has no variant) and otherwise one of its variants uniformly. `None` for an empty pool.
    pub(crate) fn draw(&self, rng: &mut ChaCha20Rng) -> Option<Value> {
        if self.total == 0 {
            return None;
        }
        let mut pick = rng.random_range(0..self.total);
        let base = self.bases.iter().find(|base| {
            if pick < base.weight {
                true
            } else {
                pick -= base.weight;
                false
            }
        })?;
        match &base.exact {
            Some(exact)
                if base.variants.is_empty()
                    || rng.random_ratio(EXACT_PROBABILITY.0, EXACT_PROBABILITY.1) =>
            {
                Some(exact.clone())
            }
            _ => {
                let index = rng.random_range(0..base.variants.len());
                base.variants.get(index).cloned()
            }
        }
    }
}

/// The pool of each hole from `harvest`, in hole order: a harvest the caller made, from the
/// campaign's own rule graph ([`Harvest::from_graph`]) or for the campaign
/// ([`Harvest::for_campaign`]).
pub(crate) fn pools(
    harvest: &Harvest,
    spec: &CampaignSpec,
    holes: &[ResolvedHole],
) -> Vec<HolePool> {
    holes
        .iter()
        .map(|hole| HolePool::new(harvest, &hole.sort, &hole.decl.constraints, &spec.bounds))
        .collect()
}

/// `literal` as a value of a hole of `sort` whose builtin domain values have the KORE sort
/// `own_sort`; `None` when it is no value of that sort.
fn literal_value(literal: &Literal, sort: &ValueSort, own_sort: Option<&str>) -> Option<Value> {
    match (literal, sort.generated()) {
        (Literal::Domain { sort: found, text }, generated) if Some(found.as_str()) == own_sort => {
            domain_value(text, generated)
        }
        (Literal::Constant { symbol }, ValueSort::Data { .. }) => {
            let value = Value::Apply {
                symbol: symbol.clone(),
                arguments: Vec::new(),
            };
            values::check_shape(&value, sort).is_ok().then_some(value)
        }
        (Literal::Domain { sort: found, text }, ValueSort::Data { .. }) => {
            // A data sort with a builtin subsort takes that builtin's values.
            let builtin = [
                ValueSort::Int,
                ValueSort::Bool,
                ValueSort::String,
                ValueSort::Bytes,
            ]
            .into_iter()
            .find(|builtin| {
                builtin.kore_sort().ok().as_ref().and_then(kore_sort_text) == Some(found.clone())
            })?;
            let value = domain_value(text, &builtin)?;
            values::check_shape(&value, sort).is_ok().then_some(value)
        }
        _ => None,
    }
}

/// The value of the builtin `sort` whose domain value has the bytes `text`.
fn domain_value(text: &[u8], sort: &ValueSort) -> Option<Value> {
    let utf8 = || std::str::from_utf8(text).ok();
    match sort {
        ValueSort::Int => utf8()?.parse::<BigInt>().ok().map(Value::Int),
        ValueSort::Bool => match utf8()? {
            "true" => Some(Value::Bool(true)),
            "false" => Some(Value::Bool(false)),
            _ => None,
        },
        ValueSort::String => utf8().map(|text| Value::String(text.to_owned())),
        ValueSort::Bytes => Some(Value::Bytes(text.to_vec())),
        ValueSort::MInt { width } => values::print::parse_mint(utf8()?, *width).ok(),
        ValueSort::Token { sort } => {
            let text = utf8()?;
            (!text.is_empty()).then(|| Value::Token {
                sort: sort.clone(),
                text: text.to_owned(),
            })
        }
        _ => None,
    }
}

/// The variants of a harvested value: `v - 3` .. `v + 3` and `-v` for an integer (for an
/// `MInt`, those inside `0 .. 2^width`, and `2^width - v` modulo `2^width`), the negation of a
/// `Bool`, and none for any other value. The value itself may be among them.
fn variants(value: &Value) -> Vec<Value> {
    let offsets = || (1..=EXPANSION).flat_map(|step| [-i64::from(step), i64::from(step)]);
    match value {
        Value::Int(number) => offsets()
            .map(|offset| Value::Int(number + offset))
            .chain([Value::Int(-number)])
            .collect(),
        Value::MInt { width, value } => {
            let modulus = BigInt::from(1u8) << *width;
            let number = BigInt::from(value.clone());
            offsets()
                .map(|offset| &number + offset)
                .chain([(&modulus - &number) % &modulus])
                .filter(|candidate| !candidate.is_negative() && *candidate < modulus)
                .filter_map(|candidate| BigUint::try_from(candidate).ok())
                .map(|value| Value::MInt {
                    width: *width,
                    value,
                })
                .collect()
        }
        Value::Bool(flag) => vec![Value::Bool(!flag)],
        _ => Vec::new(),
    }
}

/// The dictionary proposer (ARCHITECTURE 8.3; module documentation, "Drawing"). It never runs
/// out and ignores feedback: the harvest is static, and a run-time pool from matched
/// substitutions needs G-7.
pub(crate) struct DictionaryProposer {
    pools: Arc<Vec<HolePool>>,
    generators: Vec<Generator>,
    values: ValueRng,
    rng: ChaCha20Rng,
}

impl DictionaryProposer {
    /// A dictionary proposer over one pool and one generator per hole, in hole order, seeded
    /// from the campaign seed `seed`.
    pub(crate) fn new(pools: Arc<Vec<HolePool>>, generators: Vec<Generator>, seed: u64) -> Self {
        Self {
            pools,
            generators,
            values: ValueRng::from_seed(crate::engine::derive_seed(seed, "dictionary-values")),
            rng: ChaCha20Rng::from_seed(crate::engine::derive_seed(seed, "dictionary")),
        }
    }
}

impl Proposer for DictionaryProposer {
    fn kind(&self) -> ProposerKind {
        ProposerKind::Dictionary
    }

    fn propose(&mut self, _context: &mut ProposalContext<'_>) -> Option<Proposal> {
        let mut values = Vec::with_capacity(self.generators.len());
        let mut trees: Vec<Option<Box<dyn ValueShrinker>>> =
            Vec::with_capacity(self.generators.len());
        let mut failure = None;
        let (numerator, denominator) = DRAW_PROBABILITY;
        for (hole, generator) in self.generators.iter().enumerate() {
            let harvested = self
                .pools
                .get(hole)
                .filter(|pool| !pool.is_empty())
                .filter(|_| self.rng.random_ratio(numerator, denominator))
                .and_then(|pool| pool.draw(&mut self.rng));
            if let Some(value) = harvested {
                values.push(value);
                trees.push(None);
                continue;
            }
            match generator.try_generate(&mut self.values) {
                Ok(tree) => {
                    values.push(tree.current());
                    trees.push(Some(Box::new(tree)));
                }
                Err(message) => {
                    failure = Some(format!("hole {hole}: {message}"));
                    break;
                }
            }
        }
        Some(Proposal {
            origin: Origin::Scheduled(ProposerKind::Dictionary),
            values,
            trees,
            failure,
        })
    }

    fn observe(&mut self, _proposal: &Proposal, _observation: &Observation, _interesting: bool) {}
}
