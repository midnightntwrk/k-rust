//! ```toml algorithm
//! id = "backend.confluence.critical_pairs"
//! name = "load-time critical-pair check by order-sorted unification and an innermost join"
//! sites = ["check", "Context::classify", "Context::conditions"]
//! variable = "e = executable equations; p = candidate pairs: the pairs of one index and priority group, and the inner positions of each left-hand side times the equations offered at its index and family (outside stage 1, under the load's scope, only those with a relevant equation or at an argument whose second equation is rooted at an equation head or overloaded symbol); b = unifier branch states of one pair (at most UNIFIER_BRANCHES, 4,096); c = cases of one join (at most JOIN_CASES, 64); s = steps of one side (at most JOIN_STEPS, 32); t = term size"
//! counters = ["ConfluencePairs", "ConfluenceUnifierBranches", "ConfluenceJoinSteps", "ConfluenceSimplifierCalls"]
//! span = "per call"
//!
//! [[cost]]
//! mode = "one definition (check)"
//! bound = "one pass over the e equations for the rows of the constructor and overload preconditions and for the per-equation reports, each one walk of the equation's left-hand side; nothing more when no equation head or overloaded symbol can be tainted; otherwise one relevance pass over the closure's edges, visiting each equation once and marking each symbol once, with one memoized sort-reach walk per variable sort; for the self pairs of left-hand sides that may match one subject in several ways, one fixpoint per equation over its left-hand side's positions of at most as many rounds as it has variables, then p unifications of at most b branch states each, each equation renamed apart once, every branch step one substitution of O(t); per overlap one predicate simplification of the two requires and a join of at most c cases, each normalizing two sides by at most s steps, every step one match against each equation offered at the redex and one unification per equation not shown to apply; every condition first renamed canonically in O(t) and one memo lookup, its key simplified only when no earlier condition of the check renamed to it, and simplified as written instead when that key's answer could not be renamed back (twice at the key's first occurrence, once at every later one); then one closure pass per non-joined pair and one over all of them, on the closure built for relevance, each visiting an equation once and pushing a symbol once, with one memoized sort-reach walk per variable sort"
//! ```
//!
//! The load-time check that decides which value claims a definition may make.
//!
//! The backend makes two kinds of claim about an application of an equation head (an `anywhere`
//! production that is not a declared function), and about a collection: *free* (every instance
//! is a normal form, distinct from every other normal form) and *defined* (a `value-production`
//! application is defined wherever its arguments are). Both are claims about the normal-form
//! model `M_NF`: each sort is interpreted by the normal forms of the innermost evaluation
//! relation `->E` (a root step only on a term whose arguments are normal forms, priority decided
//! on those arguments), and each symbol by normalizing its application (`docs/compatibility.md`,
//! "Anywhere rules").
//!
//! `M_NF` is well defined and a model of the definition when evaluation terminates (assumed, as
//! every evaluation assumes) and the critical pairs of the executable equations join. This module
//! checks the second precondition once, when the definition is loaded:
//!
//! 1. the rows of precondition P5 (no executable equation headed by a free constructor or an
//!    injection, or indexed at a collection kind or a bare variable; overload equations of the
//!    shape `g(inj(x1), ..., inj(xn)) = inj(h(x1, ..., xn))`; a unique least common overload for
//!    any two members of a family with a common upper bound), one lookup per equation or family;
//! 2. self pairs: an equation whose left-hand side may match one subject in several ways (a map
//!    or set pattern with a key or element the rest of the left-hand side does not fix,
//!    `undetermined_variables`) is a root pair with itself; it joins when its right-hand side
//!    and `ensures` read only variables every matching binds alike, and is otherwise reported
//!    (`UnresolvedShape::SeveralMatches`);
//! 3. stage 1: the root pairs of the equations rooted at the members of each overload family,
//!    unified without the overload axioms (complete without any premise, since an overload
//!    left-hand side holds only injections of variables below its root). A family all of whose
//!    stage-1 pairs join is confluent: lowering terminates (it descends in the finite overload
//!    order) and is locally confluent, so every term has one lowest form;
//! 4. stage 2: every other root pair (two equations at one index and priority) and every inner
//!    pair (an equation `e1`, a non-variable position `q` strictly below the root of its
//!    left-hand side, and an equation `e2` offered at the head of `l1|q`, at a member of its
//!    overload family, or at a bare variable), unified over normal-form instances with the
//!    overload axioms of confluent families (`unify.rs`). Under the load's scope
//!    ([`CheckScope::Gate`]) only the pairs with a *relevant* equation, one whose closure alone
//!    reaches a symbol some gate site can be asked about, are classified: the others change no
//!    claim, whether they join or not. An inner pair at an argument of `e1` whose `e2` is rooted
//!    at an equation head or an overloaded symbol is classified under every scope: not joined,
//!    it states that `e1` is not shown consistent with `e2`, a finding the load reports whatever
//!    claims it withdraws ([`UnjoinedPair::in_argument`]);
//! 5. each overlap is separated by priority (a root pair of different priority groups), refuted
//!    (the conjunction of both `requires` simplifies to `\bottom` with every claim withheld),
//!    joined (both sides reach one term by steps valid on every instance, `join.rs`), or not
//!    joined;
//! 6. the taint closure of the non-joined pairs (`closure.rs`) names the symbols whose
//!    applications get no claim.
//!
//! Root pairs give uniqueness of normal forms: two innermost steps at one position both apply to
//! one subject whose arguments are normal forms, so their substitutions are an instance of a
//! root unifier when the equations differ, and differ only on undetermined variables when they
//! are one equation (matching modulo the map and set axioms is not unitary). Inner pairs make `M_NF` satisfy each equation at the valuations where one of its
//! subpatterns reduces. Variable positions need no pair: a variable binds a normal form, so no
//! step ever happens inside a variable's value.
//!
//! The answer is a [`ValueClaims`], stored in the definition. While it is computed the
//! definition holds `ValueClaims::withheld`, which admits no claim, so that no claim the check
//! is about to withdraw can contribute to its own verdict (a `requires` refuted through a claim,
//! a join step through a certified root). Every place that mints a claim asks
//! `ValueClaims::admit` for the index of the term it vouches for.
//!
//! Once the verdict is stored, the load adds to it the instance-normal tokens of the
//! equation-head applications written in the executable left-hand sides that denote one ground
//! term (`BackendDefinition::record_pattern_tokens`, read through `ValueClaims::pattern_token`),
//! so that equation matching reads such an application as the value it denotes, as it reads an
//! equal subject. The withheld verdict holds no token, so the check never reads one.

mod closure;
mod conditions;
mod join;
mod memo;
pub(crate) mod switches;
pub(crate) mod symbols;
#[cfg(test)]
mod tests;
mod unify;

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use rustc_hash::{FxHashMap, FxHashSet};

use k_rust_kore::measure::{self, Counter};

pub(crate) use join::SettledRoot;
pub use unify::UnresolvedShape;

use crate::{
    definition::BackendDefinition,
    instance_normal::InstanceNormal,
    rule::{
        ApartScope, Concreteness, ConstraintKind, Predicate, RewriteRule, RuleRhs, TermIndex,
        rename_apart, term_index,
    },
    simplify::{SimplificationOptions, simplify_predicate_with_solver},
    smt::NoSolver,
    substitution::{Substitution, substitute},
    term::{
        HeadRole, Name, Sort, Symbol, Term, TermKind, Variable,
        names::{FreshMarker, with_fresh_marker},
    },
};
use unify::{Families, Unifier, computed};

/// The verdict of the load-time check: which term indexes may carry value claims, and the pairs
/// that withdrew the others. Cheap to clone.
#[derive(Clone, Debug)]
pub struct ValueClaims(Arc<Verdict>);

#[derive(Clone, Debug)]
enum Verdict {
    /// The check has not run, or is running: no claim is admitted.
    Withheld,
    Checked(Box<Checked>),
}

#[derive(Clone, Debug, Default)]
struct Checked {
    tainted_symbols: BTreeSet<Name>,
    tainted_indexes: FxHashSet<TermIndex>,
    unjoined: Vec<UnjoinedPair>,
    violations: Vec<Violation>,
    counts: CheckCounts,
    /// The instance-normal tokens of the equation-head applications of executable left-hand
    /// sides that denote one ground term, recorded after the check
    /// (`BackendDefinition::record_pattern_tokens`).
    pattern_tokens: FxHashMap<Term, InstanceNormal>,
    /// Test builds: the overload families, with stage 1's verdicts.
    #[cfg(test)]
    families: Option<Families>,
}

/// The constructions of a value claim that ask the gate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum GateSite {
    /// The instance-normal scan of an equation-head application, and the equation heads it reads
    /// by their root in the left-hand sides of the equations it scans
    /// (`term::head::ScannedPatterns`).
    EquationHead,
    /// The instance-normal scan of a collection.
    Collection,
    /// The simplifier's normal-form certificate.
    Certificate,
}

impl GateSite {
    const ALL: [Self; 3] = [Self::EquationHead, Self::Collection, Self::Certificate];

    /// Whether this site can be asked about `index`: the class of indexes it vouches for. The
    /// union over the sites is the set `G` of the relevance filter ([`CheckScope::Gate`]): the
    /// gate's answers are a function of the tainted indexes in `G`, so a pair whose closure
    /// reaches no symbol of `G` changes no answer. [`ValueClaims::admit_at`] asserts in debug
    /// builds that each site asks only within its class, so a site that starts asking about
    /// another class fails until this function, and with it the filter, includes that class.
    pub(crate) fn asks_about(self, definition: &BackendDefinition, index: &TermIndex) -> bool {
        match (self, index) {
            (Self::EquationHead, TermIndex::Symbol(name)) => definition
                .symbols()
                .get(name)
                .is_some_and(|symbol| symbol.attributes.head_role() == HeadRole::EquationHead),
            (Self::Certificate, TermIndex::Symbol(name)) => definition
                .symbols()
                .get(name)
                .is_some_and(|symbol| certified_root(definition, symbol)),
            (Self::Collection, TermIndex::Map | TermIndex::List | TermIndex::Set) => true,
            _ => false,
        }
    }
}

/// Whether the simplifier's normal-form certificate can be asked for an application rooted at
/// `symbol` (`simplify::cacheable_equation_head`): an equation head, or an overloaded symbol.
pub(crate) fn certified_root(definition: &BackendDefinition, symbol: &Symbol) -> bool {
    symbol.attributes.head_role() == HeadRole::EquationHead
        || definition.overloads().is_overloaded(&symbol.name)
}

/// Whether some gate site can be asked about the index of `name`: the symbols of `G`. The other
/// indexes of `G` (collections) are tainted only by the precondition rows, never by the closure.
fn gate_symbol(definition: &BackendDefinition, name: &Name) -> bool {
    let index = TermIndex::Symbol(name.clone());
    GateSite::ALL
        .iter()
        .any(|site| site.asks_about(definition, &index))
}

/// Which candidate pairs stage 2 classifies.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CheckScope {
    /// Only the pairs one of whose equations is *relevant*: the taint closure seeded by that
    /// equation alone reaches a symbol some gate site can be asked about. Each claim this scope
    /// admits is sound on its own classification: the closure's rules have one premise each, so
    /// the closure of a union of seeds is the union of their closures, and a skipped pair's
    /// closure holds no symbol the gate is asked about whether or not the pair joins
    /// (`docs/compatibility.md`, "Anywhere rules"). When both scopes classify each pair this one
    /// classifies alike, every value claim, the taint of every such symbol and every warned pair
    /// are those of [`Self::All`]; classification reads counters that earlier pairs advance (the
    /// spelling of renamed variables) and a per-condition deadline, so that equality is tested
    /// (V9), not derived. What differs is the work counted and the non-joined pairs that withdraw
    /// no claim, which are not computed. The scope of every load.
    Gate,
    /// Every candidate pair: also the non-joined pairs of equations whose closure reaches no
    /// symbol the gate is asked about (a finding about the definition, independent of claims).
    All,
}

/// Whether the check reuses the simplification of a condition for every later condition that is
/// the same predicate up to a renaming of its free variables (`memo.rs`). The verdict is the same
/// either way; only the work differs. Every load runs [`Self::On`]; [`Self::Off`] is for the tests
/// that show the two agree.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ConditionMemo {
    On,
    Off,
}

/// Evidence that an index may carry value claims: minted only by [`ValueClaims::admit`].
#[derive(Clone, Copy, Debug)]
pub(crate) struct UntaintedIndex(());

impl ValueClaims {
    /// The verdict that admits no claim: a definition's state before and while its check runs.
    pub(crate) fn withheld() -> Self {
        Self(Arc::new(Verdict::Withheld))
    }

    /// Whether applications or collections at `index` may carry value claims: `Some` exactly
    /// when the check has run and did not taint `index`.
    #[must_use]
    pub(crate) fn admit(&self, index: &TermIndex) -> Option<UntaintedIndex> {
        match &*self.0 {
            Verdict::Withheld => None,
            Verdict::Checked(checked) => {
                (!checked.tainted_indexes.contains(index)).then_some(UntaintedIndex(()))
            }
        }
    }

    /// [`Self::admit`] at one of the gate's sites, unless a test switch admits every index there.
    /// `definition` is the definition whose verdict this is.
    #[must_use]
    pub(crate) fn admit_at(
        &self,
        definition: &BackendDefinition,
        index: &TermIndex,
        site: GateSite,
    ) -> Option<UntaintedIndex> {
        // A symbol the definition does not declare is in none of its equations, so no closure
        // taints it, in any scope.
        debug_assert!(
            site.asks_about(definition, index)
                || matches!(index, TermIndex::Symbol(name) if !definition.symbols().contains_key(name)),
            "the gate site {site:?} is asked about {index:?}, outside its class (GateSite::asks_about)"
        );
        let switches = switches::active();
        let forced = match site {
            GateSite::EquationHead => switches.admit_equation_heads,
            GateSite::Collection => false,
            GateSite::Certificate => switches.admit_certificates,
        };
        if forced {
            return Some(UntaintedIndex(()));
        }
        self.admit(index)
    }

    /// The instance-normal token the load recorded for `pattern`, an equation-head application
    /// written in an executable equation's left-hand side that denotes one ground term, or
    /// `None`: no token was recorded for it, the check has not run, or it is running. The token
    /// is that of the ground term (`BackendDefinition::record_pattern_tokens`), its own only
    /// instance, so it says that the one value `pattern` can denote is that normal form.
    #[must_use]
    pub(crate) fn pattern_token(&self, pattern: &Term) -> Option<InstanceNormal> {
        match &*self.0 {
            Verdict::Withheld => None,
            Verdict::Checked(checked) => {
                if checked.pattern_tokens.is_empty() {
                    return None;
                }
                checked.pattern_tokens.get(pattern).copied()
            }
        }
    }

    /// Record `token`, the instance-normal token of the ground term the equation-head application
    /// `pattern` denotes, after the check (`BackendDefinition::record_pattern_tokens`). A withheld
    /// verdict records nothing: no token is minted while the check runs.
    pub(crate) fn record_pattern_token(&mut self, pattern: Term, token: InstanceNormal) {
        debug_assert!(
            collapse_conjunctions(&pattern)
                .attributes()
                .variables
                .is_empty(),
            "only an application that denotes one ground term is recorded"
        );
        if let Verdict::Checked(checked) = Arc::make_mut(&mut self.0) {
            checked.pattern_tokens.insert(pattern, token);
        }
    }

    /// Test builds: a verdict that admits every index, as if the check had found nothing.
    #[cfg(test)]
    pub(crate) fn admitting_everything() -> Self {
        Self(Arc::new(Verdict::Checked(Box::default())))
    }

    /// The pairs that do not provably join and withdrew claims, in the order they were found.
    #[must_use]
    pub fn unjoined(&self) -> &[UnjoinedPair] {
        match &*self.0 {
            Verdict::Withheld => &[],
            Verdict::Checked(checked) => &checked.unjoined,
        }
    }

    /// The precondition P5 rows the definition violates.
    #[must_use]
    pub fn violations(&self) -> &[Violation] {
        match &*self.0 {
            Verdict::Withheld => &[],
            Verdict::Checked(checked) => &checked.violations,
        }
    }

    /// The symbols whose applications get no value claim, sorted by name. Only the equation
    /// heads among them change what the backend claims; the others are named because the
    /// closure passes through them.
    #[must_use]
    pub fn tainted_symbols(&self) -> Vec<Name> {
        match &*self.0 {
            Verdict::Withheld => Vec::new(),
            Verdict::Checked(checked) => checked.tainted_symbols.iter().cloned().collect(),
        }
    }

    /// The work the check did.
    #[must_use]
    pub fn counts(&self) -> CheckCounts {
        match &*self.0 {
            Verdict::Withheld => CheckCounts::default(),
            Verdict::Checked(checked) => checked.counts,
        }
    }

    /// Where this verdict and `other`, two verdicts of `definition` (in two scopes), would make
    /// different value claims or warn about different pairs: the tainted symbols some gate site
    /// can be asked about, the tainted indexes that are not symbols (the precondition rows), the
    /// gate's answer at every site for every symbol of the definition and every collection
    /// index, and the pairs that withdraw a claim (equations, position, reason, overlapped term as
    /// spelled canonically, withdrawn symbols).
    /// Empty when they agree.
    #[must_use]
    pub fn claim_differences(
        &self,
        other: &ValueClaims,
        definition: &BackendDefinition,
    ) -> Vec<String> {
        let (Verdict::Checked(left), Verdict::Checked(right)) = (&*self.0, &*other.0) else {
            return vec!["a verdict is withheld".into()];
        };
        let mut differences = Vec::new();
        let gate_tainted = |checked: &Checked| {
            checked
                .tainted_symbols
                .iter()
                .filter(|name| gate_symbol(definition, name))
                .cloned()
                .collect::<BTreeSet<_>>()
        };
        let (left_gate, right_gate) = (gate_tainted(left), gate_tainted(right));
        if left_gate != right_gate {
            differences.push(format!(
                "tainted symbols the gate is asked about: {left_gate:?} against {right_gate:?}"
            ));
        }
        let rows = |checked: &Checked| {
            checked
                .tainted_indexes
                .iter()
                .filter(|index| !matches!(index, TermIndex::Symbol(_)))
                .cloned()
                .collect::<BTreeSet<_>>()
        };
        let (left_rows, right_rows) = (rows(left), rows(right));
        if left_rows != right_rows {
            differences.push(format!(
                "tainted indexes of the rows: {left_rows:?} against {right_rows:?}"
            ));
        }
        let indexes = definition
            .symbols()
            .keys()
            .map(|name| TermIndex::Symbol(name.clone()))
            .chain([TermIndex::Map, TermIndex::List, TermIndex::Set]);
        for index in indexes {
            for site in GateSite::ALL {
                if site.asks_about(definition, &index)
                    && self.admit(&index).is_some() != other.admit(&index).is_some()
                {
                    differences.push(format!("the gate's answer at {site:?} for {index:?}"));
                }
            }
        }
        let warned = |checked: &Checked| {
            checked
                .unjoined
                .iter()
                .filter(|pair| pair.reported())
                .map(|pair| {
                    (
                        format!("{:?}", pair.first),
                        format!("{:?}", pair.second),
                        pair.position.clone(),
                        pair.reason.to_string(),
                        pair.overlap.clone(),
                        pair.withdrawn.clone(),
                    )
                })
                .collect::<BTreeSet<_>>()
        };
        let (left_warned, right_warned) = (warned(left), warned(right));
        if left_warned != right_warned {
            differences.push(format!(
                "warned pairs: {} against {}, differing in {:?}",
                left_warned.len(),
                right_warned.len(),
                left_warned
                    .symmetric_difference(&right_warned)
                    .map(|(first, second, position, reason, overlap, withdrawn)| format!(
                        "{first} / {second} at {position:?} on {overlap:?} ({reason}) withdrawing {withdrawn:?}"
                    ))
                    .collect::<Vec<_>>()
            ));
        }
        differences
    }

    /// Where this verdict and `other`, two verdicts of one definition in one scope, differ: the
    /// tainted symbols and indexes, the precondition rows (equation and kind), and every
    /// non-joined pair (equations by unique id, position, reason, overlapped term as spelled
    /// canonically, withdrawn symbols, and whether it withdraws a claim). Empty when they agree;
    /// the counts are compared by the caller ([`Self::counts`]).
    #[must_use]
    pub fn verdict_differences(&self, other: &ValueClaims) -> Vec<String> {
        let (Verdict::Checked(left), Verdict::Checked(right)) = (&*self.0, &*other.0) else {
            return vec!["a verdict is withheld".into()];
        };
        let mut differences = Vec::new();
        if left.tainted_symbols != right.tainted_symbols {
            differences.push(format!(
                "tainted symbols: {:?} against {:?}",
                left.tainted_symbols, right.tainted_symbols
            ));
        }
        let indexes = |checked: &Checked| {
            checked
                .tainted_indexes
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>()
        };
        if indexes(left) != indexes(right) {
            differences.push(format!(
                "tainted indexes: {:?} against {:?}",
                indexes(left),
                indexes(right)
            ));
        }
        let unique_id = |rule: &RewriteRule| rule.attributes.unique_id.clone();
        let rows = |checked: &Checked| {
            checked
                .violations
                .iter()
                .map(|violation| {
                    (
                        violation.rule.as_deref().map(unique_id),
                        violation.kind.to_string(),
                    )
                })
                .collect::<Vec<_>>()
        };
        if rows(left) != rows(right) {
            differences.push(format!(
                "precondition rows: {:?} against {:?}",
                rows(left),
                rows(right)
            ));
        }
        let pairs = |checked: &Checked| {
            let mut pairs = checked
                .unjoined
                .iter()
                .map(|pair| {
                    (
                        unique_id(&pair.first),
                        unique_id(&pair.second),
                        pair.position.clone(),
                        pair.reason.to_string(),
                        pair.overlap.clone(),
                        pair.withdrawn.clone(),
                        pair.relevant(),
                    )
                })
                .collect::<Vec<_>>();
            pairs.sort();
            pairs
        };
        if pairs(left) != pairs(right) {
            differences.push(format!(
                "non-joined pairs: {:?} against {:?}",
                pairs(left),
                pairs(right)
            ));
        }
        differences
    }
}

/// What the check counted.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CheckCounts {
    /// Executable equations checked.
    pub equations: usize,
    /// Candidate pairs unified (root and inner).
    pub pairs: usize,
    /// Overlaps found (unifiers of candidate pairs).
    pub overlaps: usize,
    /// Overlaps separated by priority.
    pub separated: usize,
    /// Overlaps refuted by their conditions.
    pub refuted: usize,
    /// Overlaps joined.
    pub joined: usize,
    /// Pairs not joined (including unresolved and per-equation reports).
    pub unjoined: usize,
    /// Branch states the unifier explored.
    pub unifier_branches: usize,
    /// Steps the join took.
    pub join_steps: usize,
    /// Conditions given to the predicate simplifier (to be refuted or decided), including those
    /// the memo answered. Each is answered in exactly one way, so this is the sum of
    /// `condition_memo_hits`, `key_simplifications` and `as_written_simplifications`.
    pub simplifier_calls: usize,
    /// Of those, the conditions answered from the memo of condition simplifications
    /// ([`ConditionMemo`]), with no simplification; zero with the memo off.
    pub condition_memo_hits: usize,
    /// Of those, the conditions whose memo key (the condition with its free variables renamed
    /// canonically, `memo.rs`) was simplified: one per key with the memo on, none with it off.
    pub key_simplifications: usize,
    /// Of those, the conditions simplified as written and not through their key: every
    /// condition with the memo off, and with it on each condition whose key's answer the memo
    /// refused earlier in the check.
    pub as_written_simplifications: usize,
    /// Of the key simplifications, those whose answer the memo refused (renaming it back could
    /// capture or share a variable): the condition is then simplified as written too. The
    /// simplifications run are `key_simplifications + as_written_simplifications` plus these.
    pub condition_memo_refusals: usize,
    /// Equations whose left-hand side may match one subject in several ways (a map or set
    /// pattern with an entry the rest of the left-hand side does not fix): each is a root pair
    /// with itself, counted among the overlaps and as joined or not joined.
    pub several_matches: usize,
    /// Overload families, and those found confluent by stage 1.
    pub families: usize,
    pub confluent_families: usize,
    /// Executable equations whose taint closure alone reaches a symbol some gate site can be
    /// asked about ([`CheckScope::Gate`]).
    pub relevant_equations: usize,
    /// Stage-2 candidate pairs not classified because neither equation is relevant (zero under
    /// [`CheckScope::All`]); `pairs` does not count them.
    pub skipped: usize,
}

impl CheckCounts {
    /// The counts that do not depend on the memo of condition simplifications: these, with
    /// the memo's own work (its hits, key simplifications, as-written simplifications and
    /// refusals) zeroed. The check with and without the memo agrees on them.
    #[must_use]
    pub fn without_memo_work(self) -> Self {
        Self {
            condition_memo_hits: 0,
            key_simplifications: 0,
            as_written_simplifications: 0,
            condition_memo_refusals: 0,
            ..self
        }
    }
}

/// A critical pair that does not provably join, or an executable equation that the evaluator
/// never applies as written, with what the check found.
#[derive(Clone, Debug)]
pub struct UnjoinedPair {
    /// The equation whose left-hand side holds the overlap position.
    pub first: Arc<RewriteRule>,
    /// The equation applied at the position (the first one again for a per-equation report).
    pub second: Arc<RewriteRule>,
    /// The position in `first`'s left-hand side, as argument indexes (`\and` conjuncts count as
    /// arguments 0 and 1); empty for the root.
    pub position: Vec<usize>,
    /// The overlapped term, `first`'s left-hand side under the unifier, when there is one.
    pub overlap: Option<Term>,
    /// The two one-step reducts of the overlap (`None` for `\bottom`).
    pub sides: Option<(Option<Term>, Option<Term>)>,
    /// What the join reached from each side (`None` for `\bottom`).
    pub reached: Option<(Option<Term>, Option<Term>)>,
    /// The subterm at which the join refused a step, if it refused one.
    pub refused: Option<Term>,
    pub reason: UnjoinedReason,
    /// The symbols some gate site is asked about (equation heads and overloaded symbols) that the
    /// taint closure of this pair alone withdraws, sorted: empty when the pair changes no claim.
    pub withdrawn: Vec<Name>,
    /// Whether `position` is in an argument of `first`'s left-hand side and `second` is rooted at
    /// an equation head or an overloaded symbol ([`Self::in_argument`]).
    pub rewrites_argument: bool,
}

impl UnjoinedPair {
    /// Whether the pair withdraws a value claim: the pairs the backend reports.
    #[must_use]
    pub fn relevant(&self) -> bool {
        !self.withdrawn.is_empty()
    }

    /// Whether the backend reports the pair: it withdraws a value claim, it is a report on one
    /// equation the evaluator never applies as written ([`UnjoinedReason::describes_one_equation`]),
    /// or it is an inner pair at an argument of `first` ([`Self::in_argument`]); the last two
    /// hold whether or not the definition makes claims.
    #[must_use]
    pub fn reported(&self) -> bool {
        self.relevant() || self.reason.describes_one_equation() || self.in_argument()
    }

    /// Whether the pair is an inner pair at an argument of `first`'s left-hand side whose
    /// `second` is rooted at an equation head or an overloaded symbol: `second` rewrites some
    /// instance of an argument pattern of `first`. Both equations are axioms, so at
    /// such an instance the application `first` rewrites equals both `first`'s right-hand side
    /// and the application with the rewritten argument. Not joined, the two are not shown equal,
    /// so `first` is not shown consistent with `second` there: the condition that keeps an
    /// equation with an anywhere head in an argument consistent (its argument pattern is normal
    /// on every instance, or every such pair joins) is not shown to hold
    /// (`docs/compatibility.md`, "Anywhere heads in equation arguments").
    #[must_use]
    pub fn in_argument(&self) -> bool {
        self.rewrites_argument
    }

    /// The pair's terms, in order: the overlap, the two reducts, what the join reached from
    /// each, the refused subterm.
    fn terms(&self) -> impl Iterator<Item = &Term> {
        fn both(terms: &Option<(Option<Term>, Option<Term>)>) -> [Option<&Term>; 2] {
            terms.as_ref().map_or([None, None], |(left, right)| {
                [left.as_ref(), right.as_ref()]
            })
        }
        [self.overlap.as_ref()]
            .into_iter()
            .chain(both(&self.sides))
            .chain(both(&self.reached))
            .chain([self.refused.as_ref()])
            .flatten()
    }

    /// Renames every variable the check minted in the pair's terms (a name with `!`, which no
    /// KORE identifier has: the second equation renamed apart, the unifier's and the join's
    /// fresh variables, all spelled `{base}!{marker}{counter}`, `FreshMarker`) to its base name,
    /// its marker and a counter from 0 in order of first occurrence over [`Self::terms`]. Those
    /// names otherwise carry the thread's counters, which every pair classified before this one
    /// advanced, so the same pair would be spelled differently in the two scopes or after any
    /// change to what the check classifies first.
    /// The renaming is injective (one counter for all), its names meet no variable it keeps
    /// (those have no `!`), and terms have no binders, so the terms mean what they meant.
    fn spell_canonically(&mut self) {
        let mut seen = FxHashSet::default();
        let mut order = Vec::new();
        for term in self.terms() {
            memo::first_occurrences(term, &mut seen, &mut order);
        }
        let renaming = order
            .into_iter()
            .filter(|variable| variable.name.contains('!'))
            .enumerate()
            .map(|(counter, variable)| {
                let (base, minted) = variable
                    .name
                    .split_once('!')
                    .expect("the filter keeps names with `!`");
                let marker = minted
                    .split(|character: char| !character.is_ascii_alphabetic())
                    .next()
                    .unwrap_or_default();
                let name = format!("{base}!{marker}{counter}");
                let renamed = Term::variable(variable.with_name(name));
                (variable, renamed)
            })
            .collect::<Substitution>();
        if renaming.is_empty() {
            return;
        }
        let rename = |term: &mut Option<Term>| {
            if let Some(term) = term {
                *term = substitute(term, &renaming);
            }
        };
        rename(&mut self.overlap);
        for terms in [&mut self.sides, &mut self.reached].into_iter().flatten() {
            rename(&mut terms.0);
            rename(&mut terms.1);
        }
        rename(&mut self.refused);
    }
}

/// Why a pair does not provably join.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum UnjoinedReason {
    /// The join ended in two different terms.
    DifferentResults,
    /// The join ran out of steps or term size.
    JoinBudget,
    /// The join refused a step that would bind or erase a subterm it could not show defined.
    JoinRefused,
    /// The sides differ and a `requires` of the pair is neither refuted nor shown to hold.
    ConditionOpen,
    /// The two equations' `ensures` differ at the overlap.
    EnsuresDiffer,
    /// The unifier met a shape it does not decide.
    Unresolved(UnresolvedShape),
    /// The equation's right-hand side or `ensures` has variables its left-hand side does not
    /// bind: the evaluator never applies it, yet it is an axiom.
    UnboundResultVariables,
    /// The equation's left-hand side holds an application of a declared function, a macro or an
    /// uninterpreted symbol below its root: the evaluator applies it only where the subject
    /// spells that application, never where the argument holds the value the application
    /// computes, yet it is an axiom.
    ComputedBelowRoot(Name),
    /// A right-hand side the join does not read (a disjunction, `\top` or predicates).
    UnsupportedRightHandSide,
}

impl UnjoinedReason {
    /// Whether the reason is about one equation alone, not a pair: an equation the evaluator does
    /// not apply to every subject it describes, although the definition states it as an axiom.
    #[must_use]
    pub fn describes_one_equation(&self) -> bool {
        matches!(
            self,
            Self::UnboundResultVariables | Self::ComputedBelowRoot(_)
        )
    }
}

impl std::fmt::Display for UnjoinedReason {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DifferentResults => formatter.write_str("the two reducts reach different terms"),
            Self::JoinBudget => formatter.write_str("the join ran out of steps or cases"),
            Self::JoinRefused => formatter.write_str(
                "a join step would bind or erase a subterm not shown defined on every instance",
            ),
            Self::ConditionOpen => {
                formatter.write_str("the conditions are neither refuted nor enough to join")
            }
            Self::EnsuresDiffer => formatter.write_str("the two equations' ensures differ"),
            Self::Unresolved(shape) => write!(formatter, "the overlap has {shape}"),
            Self::UnboundResultVariables => formatter
                .write_str("the right-hand side has variables the left-hand side does not bind"),
            Self::ComputedBelowRoot(symbol) => write!(
                formatter,
                "the left-hand side holds an application of `{symbol}` below its root, which the evaluator never rewrites to it"
            ),
            Self::UnsupportedRightHandSide => {
                formatter.write_str("the right-hand side is not a term")
            }
        }
    }
}

impl std::fmt::Display for ViolationKind {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ConstructorHeaded(symbol) => {
                write!(
                    formatter,
                    "an executable equation is headed by the constructor `{symbol}`"
                )
            }
            Self::InjectionHeaded => {
                formatter.write_str("an executable equation is headed by a sort injection")
            }
            Self::IndexedAt(index) => {
                write!(formatter, "an executable equation is indexed at {index:?}")
            }
            Self::OverloadShape(symbol) => write!(
                formatter,
                "an overload equation of `{symbol}` does not have the shape g(inj(x1), ..., inj(xn)) = inj(h(x1, ..., xn))"
            ),
            Self::NoLeastCommonOverload(left, right) => write!(
                formatter,
                "the overloads `{left}` and `{right}` have no unique least common overload"
            ),
            Self::PinnedByInjectiveTotal(symbol) => write!(
                formatter,
                "`{symbol}` is total and injective into a hooked sort, so no model keeps the values its arguments can hold apart"
            ),
        }
    }
}

/// A violated row of precondition P5.
#[derive(Clone, Debug)]
pub struct Violation {
    pub rule: Option<Arc<RewriteRule>>,
    pub kind: ViolationKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ViolationKind {
    /// An executable equation headed by a free constructor (its name).
    ConstructorHeaded(Name),
    /// An executable equation headed by an injection.
    InjectionHeaded,
    /// An executable equation indexed at a collection kind or a bare variable.
    IndexedAt(TermIndex),
    /// An overload equation of the family of this symbol that does not have the shape
    /// `g(inj(x1), ..., inj(xn)) = inj(h(x1, ..., xn))`.
    OverloadShape(Name),
    /// Two members of one family with a common upper bound and no unique least one.
    NoLeastCommonOverload(Name, Name),
    /// A total injective symbol into a hooked sort whose argument sorts can hold equation
    /// heads: no model of the construction interprets it on new elements, so those heads get no
    /// value claims (the symbol table, `symbols.rs`).
    PinnedByInjectiveTotal(Name),
}

impl ViolationKind {
    /// Whether the row withdraws value claims (taints) rather than only reporting a premise the
    /// claims rest on.
    #[must_use]
    pub fn withdraws(&self) -> bool {
        match self {
            Self::ConstructorHeaded(_)
            | Self::InjectionHeaded
            | Self::IndexedAt(_)
            | Self::PinnedByInjectiveTotal(_) => true,
            Self::OverloadShape(_) | Self::NoLeastCommonOverload(..) => false,
        }
    }
}

/// An executable equation of the check.
struct Equation {
    rule: Arc<RewriteRule>,
    index: TermIndex,
}

/// Whether `rule` is restricted to symbolic instances: such an equation is never a step on a
/// ground term, so it is not a step of `->E` (precondition P4 states it as a theorem).
fn symbolic(rule: &RewriteRule) -> bool {
    match &rule.attributes.concreteness {
        Concreteness::Unconstrained => false,
        Concreteness::All(kind) => *kind == ConstraintKind::Symbolic,
        Concreteness::Some(constraints) => constraints
            .values()
            .any(|kind| *kind == ConstraintKind::Symbolic),
    }
}

/// The left-hand side's non-variable proper subterms, each with its position: argument indexes
/// through applications and collections (in `every_immediate_subterm` order), 0 for an
/// injection's operand, and 0 or 1 for the conjuncts of an `\and`.
fn inner_positions(lhs: &Term) -> Vec<(Vec<usize>, Term)> {
    let mut positions = Vec::new();
    let mut stack = vec![(Vec::new(), lhs.clone())];
    while let Some((path, term)) = stack.pop() {
        if !path.is_empty() && !matches!(term.kind(), TermKind::Variable(_) | TermKind::And(..)) {
            positions.push((path.clone(), term.clone()));
        }
        for (index, child) in children(&term).into_iter().enumerate().rev() {
            let mut child_path = path.clone();
            child_path.push(index);
            stack.push((child_path, child));
        }
    }
    positions
}

/// Whether `path` (an [`inner_positions`] position) leads into an argument of `lhs`: it passes
/// below some term that is not an `\and`. A path through `\and` conjuncts alone reaches a
/// conjunct, which is the left-hand side's root, not one of its arguments.
fn argument_position(lhs: &Term, path: &[usize]) -> bool {
    let mut term = lhs.clone();
    for index in path {
        if !matches!(term.kind(), TermKind::And(..)) {
            return true;
        }
        term = children(&term)[*index].clone();
    }
    false
}

/// The immediate subterms of `term`, in the order positions count them.
fn children(term: &Term) -> Vec<Term> {
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

/// `term` with its children replaced by `children`, in [`children`] order.
fn with_children(term: &Term, mut new: Vec<Term>) -> Term {
    match term.kind() {
        TermKind::Application {
            symbol,
            sort_arguments,
            ..
        } => Term::application(symbol.clone(), sort_arguments.clone(), new),
        TermKind::Injection { source, target, .. } => {
            Term::injection(source.clone(), target.clone(), new.remove(0))
        }
        TermKind::And(..) => {
            let right = new.remove(1);
            Term::and(new.remove(0), right)
        }
        TermKind::Map {
            definition,
            entries,
            rest,
        } => {
            let rest = rest.as_ref().map(|_| new.pop().expect("the rest"));
            let mut new = new.into_iter();
            let entries = (0..entries.len())
                .map(|_| {
                    let key = new.next().expect("a key");
                    (key, new.next().expect("a value"))
                })
                .collect();
            Term::map(definition.clone(), entries, rest)
        }
        TermKind::List {
            definition,
            heads,
            rest,
        } => {
            let mut new = new.into_iter();
            let new_heads = (0..heads.len())
                .map(|_| new.next().expect("a head"))
                .collect();
            let rest = rest.as_ref().map(|(_, tails)| {
                let middle = new.next().expect("the middle");
                (
                    middle,
                    (0..tails.len())
                        .map(|_| new.next().expect("a tail"))
                        .collect(),
                )
            });
            Term::list(definition.clone(), new_heads, rest)
        }
        TermKind::Set {
            definition,
            elements,
            rest,
        } => {
            let rest = rest.as_ref().map(|_| new.pop().expect("the rest"));
            new.truncate(elements.len());
            Term::set(definition.clone(), new, rest)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => term.clone(),
    }
}

/// The subterm of `term` at `path`.
fn subterm_at(term: &Term, path: &[usize]) -> Term {
    path.iter()
        .fold(term.clone(), |term, index| children(&term)[*index].clone())
}

/// `term` with the subterm at `path` replaced by `replacement`; an `\and` the path enters is
/// replaced by the conjunct the path enters, since after the step at `path` the term there is no
/// longer an instance of the other conjunct.
fn replace_at(term: &Term, path: &[usize], replacement: Term) -> Term {
    let Some((first, rest)) = path.split_first() else {
        return replacement;
    };
    let mut new = children(term);
    let replaced = replace_at(&new[*first], rest, replacement);
    if matches!(term.kind(), TermKind::And(..)) {
        return replaced;
    }
    new[*first] = replaced;
    with_children(term, new)
}

/// `pattern` with every `\and` replaced by one conjunct: the structured one when the other is a
/// variable (an alias, whose value under a unifier is the structured one's), else the left one.
/// Under a unifier of the pattern the two conjuncts denote one term, so the instance of the
/// result is the instance of the pattern.
pub(crate) fn collapse_conjunctions(pattern: &Term) -> Term {
    match pattern.kind() {
        TermKind::And(left, right) => {
            if matches!(left.kind(), TermKind::Variable(_)) {
                collapse_conjunctions(right)
            } else {
                collapse_conjunctions(left)
            }
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => pattern.clone(),
        _ => with_children(
            pattern,
            children(pattern)
                .iter()
                .map(collapse_conjunctions)
                .collect(),
        ),
    }
}

/// Whether a term holds an application of a declared function, a macro or alias, or an
/// uninterpreted symbol strictly below its root; the first such symbol.
fn computed_below_root(term: &Term) -> Option<Name> {
    let mut found = None;
    for child in children(term) {
        child.visit_symbols(&mut |symbol| {
            if found.is_none() && computed(symbol) {
                found = Some(symbol.name.clone());
            }
        });
    }
    found
}

/// The variables of the left-hand side `lhs` that a matching against a subject may bind to
/// different values (R2.2): matching modulo the map and set axioms is finitary, not unitary.
///
/// A position of `lhs` is *fixed* when the subject's subterm there is a function of the subject
/// and of the variables already known to be determined: the root; the children of a fixed
/// application, injection, `\and` or list (a list holds at most one rest, so its length fixes
/// every element's offset); an entry of a fixed map or set whose key's (element's) variables are
/// all determined, since a map binds each key once and a set holds each element once
/// (concatenation is nilpotent), or which is the only entry not fixed in a collection without a
/// rest; and the rest of a fixed map or set whose entries are all fixed. The variables at fixed
/// positions are determined. The operator is monotone on the finite set of `lhs`'s variables, so
/// iterating it from the empty set reaches its least fixpoint in at most that many rounds. Every
/// two matchings of `lhs` against one subject agree on the determined variables (by induction on
/// the rounds: at each fixed position both see the same subterm of the subject), so an empty
/// result means that `lhs` matches in at most one way.
pub(crate) fn undetermined_variables(lhs: &Term) -> BTreeSet<Variable> {
    fn visit(term: &Term, determined: &mut BTreeSet<Variable>) {
        let fixed_key = |key: &Term, determined: &BTreeSet<Variable>| {
            key.attributes().variables.is_subset(determined)
        };
        match term.kind() {
            TermKind::Variable(variable) => {
                determined.insert(variable.clone());
            }
            TermKind::DomainValue { .. } => {}
            TermKind::Application { .. }
            | TermKind::Injection { .. }
            | TermKind::And(..)
            | TermKind::List { .. } => {
                for child in children(term) {
                    visit(&child, determined);
                }
            }
            TermKind::Map { entries, rest, .. } => {
                let open = entries
                    .iter()
                    .filter(|(key, _)| !fixed_key(key, determined))
                    .count();
                let sole = open == 1 && rest.is_none();
                for (key, value) in entries {
                    if sole || fixed_key(key, determined) {
                        visit(key, determined);
                        visit(value, determined);
                    }
                }
                if let Some(rest) = rest
                    && open == 0
                {
                    visit(rest, determined);
                }
            }
            TermKind::Set { elements, rest, .. } => {
                let open = elements
                    .iter()
                    .filter(|element| !fixed_key(element, determined))
                    .count();
                let sole = open == 1 && rest.is_none();
                for element in elements {
                    if sole || fixed_key(element, determined) {
                        visit(element, determined);
                    }
                }
                if let Some(rest) = rest
                    && open == 0
                {
                    visit(rest, determined);
                }
            }
        }
    }
    let mut determined = BTreeSet::new();
    loop {
        let before = determined.len();
        visit(lhs, &mut determined);
        if determined.len() == before {
            break;
        }
    }
    lhs.attributes()
        .variables
        .iter()
        .filter(|variable| !determined.contains(*variable))
        .cloned()
        .collect()
}

/// The term a right-hand side denotes, `None` for `\bottom`; `Err` for a right-hand side the
/// join does not read.
fn right_hand_side(rule: &RewriteRule) -> Result<Option<Term>, ()> {
    match &rule.rhs {
        RuleRhs::Term(term) => Ok(Some(term.clone())),
        RuleRhs::Bottom => Ok(None),
        RuleRhs::Disjunction(_) | RuleRhs::Top | RuleRhs::Predicates(_) => Err(()),
    }
}

/// Executable equations by index and priority.
type Groups = BTreeMap<TermIndex, BTreeMap<u8, Vec<Arc<RewriteRule>>>>;

/// The state of one check.
pub(crate) struct Context<'d> {
    definition: &'d BackendDefinition,
    families: Families,
    /// The sorts that may have a normal form, and those with an element in every model
    /// (`symbols.rs`).
    sorts: symbols::Sorts,
    /// The executable equations, by index and priority, as equation selection offers them.
    groups: Groups,
    /// Each executable equation renamed apart, every variable to a fresh `!apart` name, made on
    /// its first use as a pair's second equation and shared by all its pairs (keyed by the
    /// equation's address; the equations live in `groups` for the whole check).
    renamed: FxHashMap<*const RewriteRule, Arc<RewriteRule>>,
    /// The simplified conditions, keyed up to a renaming of their free variables; `None` with
    /// [`ConditionMemo::Off`].
    memo: Option<memo::Memo>,
    fresh: u64,
    counts: CheckCounts,
}

impl<'d> Context<'d> {
    fn unifier<'a>(
        &'a mut self,
        lifting: bool,
        known_normal: &'a dyn Fn(&Term) -> bool,
    ) -> Unifier<'a> {
        Unifier {
            definition: self.definition,
            families: &self.families,
            lifting,
            known_normal,
            fresh: &mut self.fresh,
            branches: 0,
        }
    }

    /// Unify, counting the branches.
    fn unify(
        &mut self,
        lifting: bool,
        known_normal: &dyn Fn(&Term) -> bool,
        left: &Term,
        right: &Term,
    ) -> Result<Vec<Substitution>, UnresolvedShape> {
        let mut unifier = self.unifier(lifting, known_normal);
        let result = unifier.unify(left, right);
        let branches = unifier.branches;
        self.counts.unifier_branches += branches;
        measure::add(Counter::ConfluenceUnifierBranches, branches as u64);
        result
    }

    /// The executable equations equation selection offers a term at `index` (those indexed
    /// there or at a bare variable), every priority.
    fn offered(&self, index: &TermIndex) -> Vec<Arc<RewriteRule>> {
        let mut indexes = vec![index.clone()];
        if index != &TermIndex::Variable {
            indexes.push(TermIndex::Variable);
        }
        indexes
            .iter()
            .filter_map(|index| self.groups.get(index))
            .flat_map(|groups| groups.values().flatten().cloned())
            .collect()
    }

    /// The candidates of an inner position whose subterm is at `index`: the executable equations
    /// offered there, and those offered at the other members of `index`'s overload family.
    fn candidates(&self, index: &TermIndex) -> Vec<Arc<RewriteRule>> {
        let mut indexes = vec![index.clone()];
        if let TermIndex::Symbol(name) = index
            && let Some(family) = self.families.family(name)
        {
            indexes.extend(
                self.families
                    .members(family)
                    .iter()
                    .filter(|member| *member != name)
                    .map(|member| TermIndex::Symbol(member.clone())),
            );
        }
        if index != &TermIndex::Variable {
            indexes.push(TermIndex::Variable);
        }
        indexes
            .iter()
            .filter_map(|index| self.groups.get(index))
            .flat_map(|groups| groups.values().flatten().cloned())
            .collect()
    }

    /// Whether the conjunction of `requires` instantiated by `substitution` holds on no instance.
    fn refuted(&mut self, rules: &[&RewriteRule], substitution: &Substitution) -> bool {
        matches!(self.conditions(rules, substitution), Conditions::Refuted)
    }

    /// What the conjunction of `requires` instantiated by `substitution` says, simplified with no
    /// assumption, no solver and every claim withheld (the definition holds
    /// [`ValueClaims::withheld`]): refuted when it simplifies to `\bottom` or its conjuncts are
    /// contradictory (`conditions.rs`), else the equalities between a variable and a term that
    /// every instance satisfying it has. Each simplification step is an axiom instance that
    /// carries its bindings' definedness, so a `\bottom` holds in every model.
    fn conditions(&mut self, rules: &[&RewriteRule], substitution: &Substitution) -> Conditions {
        let predicates = rules
            .iter()
            .flat_map(|rule| {
                rule.requires
                    .instantiate(substitution)
                    .with_definedness(self.definition, &[])
            })
            .collect::<Vec<_>>();
        if predicates.is_empty() {
            return Conditions::Open(Substitution::new());
        }
        if switches::active().refute_every_condition {
            return Conditions::Refuted;
        }
        let Some(simplified) = self.simplify(Predicate::And(predicates)) else {
            return Conditions::Open(Substitution::new());
        };
        let mut conjuncts = BTreeSet::new();
        flatten(simplified, &mut conjuncts);
        let conjuncts = conjuncts.into_iter().collect::<Vec<_>>();
        if conjuncts.contains(&Predicate::False) || conditions::contradictory(&conjuncts) {
            return Conditions::Refuted;
        }
        Conditions::Open(conditions::equalities(&conjuncts))
    }

    /// The predicate simplified with no assumption and no solver, `None` on a failure or stop:
    /// from the memo when a predicate that renames to the same key was simplified before
    /// (`memo.rs`); else by [`Self::simplify_now`], of the predicate as written when the memo is
    /// off or refused that key's answer before, and otherwise of the key, then of the predicate
    /// as written if the memo refuses the key's answer.
    fn simplify(&mut self, predicate: Predicate) -> Option<Predicate> {
        self.counts.simplifier_calls += 1;
        measure::bump(Counter::ConfluenceSimplifierCalls);
        let Some(memo) = &self.memo else {
            self.counts.as_written_simplifications += 1;
            return self.simplify_now(predicate);
        };
        let canonical = match memo.lookup(&predicate) {
            memo::Lookup::Hit(answer) => {
                self.counts.condition_memo_hits += 1;
                return answer;
            }
            memo::Lookup::AsWritten => {
                self.counts.as_written_simplifications += 1;
                return self.simplify_now(predicate);
            }
            memo::Lookup::Miss(canonical) => canonical,
        };
        self.counts.key_simplifications += 1;
        let answer = self.simplify_now(canonical.key.clone());
        let memo = self.memo.as_mut().expect("the memo is on");
        match memo.store(canonical, answer) {
            Ok(answer) => answer,
            Err(()) => {
                self.counts.condition_memo_refusals += 1;
                self.simplify_now(predicate)
            }
        }
    }

    /// The predicate simplified with no assumption and no solver, `None` on a failure or stop.
    ///
    /// A condition of a definition whose evaluation does not end (outside precondition P0) can
    /// keep the simplifier evaluating without bound, so each call runs under a step deadline of
    /// [`CONDITION_SECONDS`]; a stopped call decides nothing. Under P0 every condition the
    /// corpus has simplifies in microseconds, far from it. The check runs detached from the
    /// loading request ([`check`]), so that deadline, and a stack-exhaustion stop on a condition
    /// far deeper than any in the corpus, are the only stops it can meet; both lose precision
    /// only. `wasm32` has no clock: there a condition outside P0 keeps the load from ending, as
    /// an evaluation of it would.
    fn simplify_now(&mut self, predicate: Predicate) -> Option<Predicate> {
        #[cfg(not(target_arch = "wasm32"))]
        let _deadline = {
            let limit = std::time::Duration::from_secs(CONDITION_SECONDS);
            crate::stop::arm_deadline(
                std::time::Instant::now() + limit,
                crate::timeout::StepTimeoutMode::Manual(limit),
            )
        };
        match simplify_predicate_with_solver(
            self.definition,
            &predicate,
            &[],
            SimplificationOptions {
                max_iterations: CONDITION_ITERATIONS,
                ..SimplificationOptions::default()
            },
            &NoSolver,
        ) {
            Ok(Ok(simplified)) => Some(simplified),
            Ok(Err(_)) => None,
            Err(stop) => {
                stop.into_cause();
                None
            }
        }
    }
}

/// Test builds: unify `left` and `right` over normal-form instances of `definition` as stage 2
/// does: with the overload axioms of the families stage 1 found confluent.
#[cfg(test)]
pub(crate) fn unify_for_tests(
    definition: &BackendDefinition,
    left: &Term,
    right: &Term,
) -> Result<Vec<Substitution>, UnresolvedShape> {
    let families = match &*definition.value_claims().0 {
        Verdict::Checked(checked) => checked
            .families
            .clone()
            .unwrap_or_else(|| Families::of(definition)),
        Verdict::Withheld => Families::of(definition),
    };
    let mut fresh = 0;
    let nothing_normal = |_: &Term| false;
    Unifier {
        definition,
        families: &families,
        lifting: true,
        known_normal: &nothing_normal,
        fresh: &mut fresh,
        branches: 0,
    }
    .unify(left, right)
}

/// Test builds: relevance computed by the backward pass (`Closure::relevant`) against its
/// definition, the closure seeded by each executable equation alone meeting `G`
/// (`Closure::taint`), under the switches in force: the number of equations, the number found
/// relevant, and a description of each equation on which the two differ.
#[cfg(test)]
pub(crate) fn relevance_disagreements(
    definition: &BackendDefinition,
) -> (usize, usize, Vec<String>) {
    let (_, equations) = executable_equations(definition);
    let sorts = symbols::Sorts::of(definition);
    let mut closure = closure::Closure::new(definition, &sorts, &equations);
    let gate = |symbol: &Name| gate_symbol(definition, symbol);
    let relevant = closure.relevant(&gate);
    let mut disagreements = Vec::new();
    for (equation, relevant) in equations.iter().zip(&relevant) {
        let tainted = closure.taint([&equation.rule], []);
        let expected = tainted.iter().any(gate);
        if expected != *relevant {
            disagreements.push(format!(
                "{:?}: relevant {relevant}, its closure {tainted:?}",
                equation.rule.lhs
            ));
        }
    }
    let found = relevant.iter().filter(|relevant| **relevant).count();
    (equations.len(), found, disagreements)
}

/// Test builds: one candidate pair's unification, as [`recording_overlaps`] records it.
#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct RecordedOverlap {
    pub(crate) first: Arc<RewriteRule>,
    /// The second equation, renamed apart from the first.
    pub(crate) second: Arc<RewriteRule>,
    pub(crate) position: Vec<usize>,
    pub(crate) unifiers: Result<Vec<Substitution>, UnresolvedShape>,
}

#[cfg(test)]
thread_local! {
    static RECORDED: std::cell::RefCell<Option<Vec<RecordedOverlap>>> =
        const { std::cell::RefCell::new(None) };
}

/// Test builds: runs `run` and returns, beside its result, every candidate pair the checks it
/// ran on this thread unified, with the unifiers.
#[cfg(test)]
pub(crate) fn recording_overlaps<R>(run: impl FnOnce() -> R) -> (R, Vec<RecordedOverlap>) {
    let previous = RECORDED.replace(Some(Vec::new()));
    let result = run();
    let recorded = RECORDED.replace(previous).unwrap_or_default();
    (result, recorded)
}

/// The seconds a condition of the check may take to simplify (see `Context::simplify`).
const CONDITION_SECONDS: u64 = 1;

/// The equation iterations a condition of the check may take to simplify. A condition the
/// simplifier does not decide within it is neither refuted nor shown to hold, which loses
/// precision only.
const CONDITION_ITERATIONS: usize = 64;

/// What a pair's conditions say at a unifier.
enum Conditions {
    /// They hold on no instance.
    Refuted,
    /// They may hold; every instance where they do satisfies these equalities.
    Open(Substitution),
}

/// One candidate pair: `first`'s left-hand side at `position` against `second`'s.
struct Candidate<'r> {
    first: &'r Arc<RewriteRule>,
    second: &'r Arc<RewriteRule>,
    position: Vec<usize>,
    lifting: bool,
}

/// What classifying one candidate pair found.
enum Classified {
    /// No overlap, or every overlap separated, refuted or joined.
    Fine,
    NotJoined(Box<UnjoinedPair>),
}

impl Context<'_> {
    fn classify(&mut self, candidate: &Candidate<'_>) -> Classified {
        self.counts.pairs += 1;
        measure::bump(Counter::ConfluencePairs);
        let first = candidate.first;
        let second = if switches::active().no_rename_apart {
            Arc::clone(candidate.second)
        } else {
            self.renamed_apart(first, candidate.second)
        };
        let not_joined = |reason: UnjoinedReason| {
            Classified::NotJoined(Box::new(unjoined_report(candidate, reason)))
        };
        let inner = subterm_at(&first.lhs, &candidate.position);
        // `second` rewrites a term of its own sort: at a position of a greater sort it applies
        // under an injection, and at a position of any other sort never.
        let (inner_sort, second_sort) = (inner.sort(), second.lhs.sort());
        let injected = inner_sort != second_sort;
        if injected
            && (switches::active().drop_injected_inner
                || self
                    .definition
                    .sort_graph()
                    .check_subsort(&second_sort, &inner_sort)
                    != Ok(true))
        {
            return Classified::Fine;
        }
        let nothing_normal = |_: &Term| false;
        // The overlap must also be an instance of the rest of `first`'s left-hand side: each
        // alias `\and(a, b)` in it denotes one term, which unifying the subterm at a position
        // below it does not constrain.
        let mut equations = vec![(inner, second.lhs.clone())];
        aliases(&first.lhs, &mut equations);
        let unifiers = {
            let mut unifier = self.unifier(candidate.lifting, &nothing_normal);
            let result = unifier.unify_all(equations);
            let branches = unifier.branches;
            self.counts.unifier_branches += branches;
            measure::add(Counter::ConfluenceUnifierBranches, branches as u64);
            #[cfg(test)]
            RECORDED.with_borrow_mut(|recorded| {
                if let Some(recorded) = recorded {
                    recorded.push(RecordedOverlap {
                        first: Arc::clone(first),
                        second: Arc::clone(&second),
                        position: candidate.position.clone(),
                        unifiers: result.clone(),
                    });
                }
            });
            match result {
                Ok(unifiers) => unifiers,
                Err(shape) => return not_joined(UnjoinedReason::Unresolved(shape)),
            }
        };
        for unifier in unifiers {
            if self.vacuous(first, &second, &unifier) {
                self.counts.separated += 1;
                continue;
            }
            self.counts.overlaps += 1;
            let equalities = match self.conditions(&[first.as_ref(), second.as_ref()], &unifier) {
                Conditions::Refuted => {
                    self.counts.refuted += 1;
                    continue;
                }
                Conditions::Open(equalities) => equalities,
            };
            let instantiate = |term: &Term| substitute(&collapse_conjunctions(term), &unifier);
            let ensures = |rule: &RewriteRule| -> BTreeSet<Predicate> {
                let mut conjuncts = BTreeSet::new();
                flatten(rule.ensures.instantiate(&unifier).report(), &mut conjuncts);
                conjuncts
            };
            let overlap = instantiate(&first.lhs);
            if ensures(first) != ensures(&second) && !switches::active().ignore_ensures {
                return Classified::NotJoined(Box::new(UnjoinedPair {
                    overlap: Some(overlap),
                    ..unjoined_report(candidate, UnjoinedReason::EnsuresDiffer)
                }));
            }
            let (Ok(first_rhs), Ok(second_rhs)) =
                (right_hand_side(first), right_hand_side(&second))
            else {
                return Classified::NotJoined(Box::new(UnjoinedPair {
                    overlap: Some(overlap),
                    ..unjoined_report(candidate, UnjoinedReason::UnsupportedRightHandSide)
                }));
            };
            let first_side = first_rhs.map(|rhs| instantiate(&rhs));
            let second_side = if candidate.position.is_empty() {
                second_rhs.map(|rhs| instantiate(&rhs))
            } else {
                // The step of `second` at the position, inside `first`'s left-hand side.
                second_rhs.map(|rhs| {
                    let marker = Variable::new(
                        with_fresh_marker("VarOverlapStep", FreshMarker::Unify, self.fresh),
                        inner_sort.clone(),
                    );
                    self.fresh += 1;
                    let stepped = replace_at(
                        &first.lhs,
                        &candidate.position,
                        Term::variable(marker.clone()),
                    );
                    let mut reduct = substitute(&rhs, &unifier);
                    if injected {
                        reduct = Term::injection(second_sort.clone(), inner_sort.clone(), reduct);
                    }
                    let mut with_step = unifier.clone();
                    with_step.insert(marker, reduct);
                    substitute(&collapse_conjunctions(&stepped), &with_step)
                })
            };
            // The values the unifier gives the variables of either left-hand side are normal
            // forms on every instance the pair speaks about: they are subterms of an innermost
            // redex's normal-form arguments, or of an outer equation's valuation by elements.
            let values = first
                .lhs
                .attributes()
                .variables
                .iter()
                .chain(second.lhs.attributes().variables.iter())
                .map(|variable| {
                    unifier
                        .get(variable)
                        .cloned()
                        .unwrap_or_else(|| Term::variable(variable.clone()))
                })
                .collect::<Vec<_>>();
            let conditional = !first.requires.is_empty() || !second.requires.is_empty();
            // Only the instances where both conditions hold are peaks, and each of them
            // satisfies the conditions' equalities.
            // The values stay as the unifier built them: they are instances of patterns, which
            // the join reads as normal forms, while an equality may give a variable the value of
            // any term.
            let under =
                |term: &Option<Term>| term.as_ref().map(|term| substitute(term, &equalities));
            let (first_side, second_side) = (under(&first_side), under(&second_side));
            match join::join(
                self,
                candidate.lifting,
                (first_side.clone(), second_side.clone()),
                &values,
            ) {
                join::Outcome::Joined => self.counts.joined += 1,
                join::Outcome::NotJoined {
                    reached,
                    refused,
                    reason,
                } => {
                    let reason = match reason {
                        UnjoinedReason::DifferentResults if conditional => {
                            UnjoinedReason::ConditionOpen
                        }
                        reason => reason,
                    };
                    return Classified::NotJoined(Box::new(UnjoinedPair {
                        overlap: Some(overlap),
                        sides: Some((first_side, second_side)),
                        reached: Some(reached),
                        refused,
                        ..unjoined_report(candidate, reason)
                    }));
                }
            }
        }
        Classified::Fine
    }
}

impl Context<'_> {
    /// `second` with variables disjoint from `first`'s: its shared copy with every variable
    /// renamed to a fresh `!apart` name ([`rename_apart`] against its own variables), made once
    /// per equation. A renaming of an equation's variables is the same equation, and the first
    /// equation of a pair is an equation of the definition, whose variables no `!apart` renaming
    /// minted, so the copy is apart from it; the disjointness is still tested (two sorted sets),
    /// and on a clash the equation is renamed apart from `first` alone, as for one pair.
    fn renamed_apart(
        &mut self,
        first: &Arc<RewriteRule>,
        second: &Arc<RewriteRule>,
    ) -> Arc<RewriteRule> {
        let shared =
            self.renamed.entry(Arc::as_ptr(second)).or_insert_with(|| {
                match rename_apart(second, &second.computed_attributes.variables, &[]) {
                    Some((renamed, _)) => Arc::new(renamed),
                    None => Arc::clone(second),
                }
            });
        if shared
            .computed_attributes
            .variables
            .is_disjoint(&first.computed_attributes.variables)
        {
            return Arc::clone(shared);
        }
        match rename_apart(second, &first.computed_attributes.variables, &[]) {
            Some((renamed, _)) => Arc::new(renamed),
            None => Arc::clone(second),
        }
    }
}

/// The pairs of conjuncts of every `\and` in `pattern`.
fn aliases(pattern: &Term, into: &mut Vec<(Term, Term)>) {
    if let TermKind::And(left, right) = pattern.kind() {
        into.push((left.clone(), right.clone()));
    }
    for child in children(pattern) {
        aliases(&child, into);
    }
}

impl Context<'_> {
    /// Whether the overlap has no instance: some variable it ranges over has a sort with no
    /// normal form.
    fn vacuous(&self, first: &RewriteRule, second: &RewriteRule, unifier: &Substitution) -> bool {
        // Only a declared sort without parameters is judged; any other is counted inhabited.
        let uninhabited = |variable: &Variable| match &variable.sort {
            Sort::Application { name, arguments } => {
                arguments.is_empty()
                    && self
                        .definition
                        .sorts()
                        .get(name)
                        .is_some_and(|info| info.parameters.is_empty())
                    && !self.sorts.has_normal_form(&variable.sort)
            }
            Sort::Variable(_) => false,
        };
        first
            .lhs
            .attributes()
            .variables
            .iter()
            .chain(second.lhs.attributes().variables.iter())
            .any(|variable| match unifier.get(variable) {
                Some(value) => value.attributes().variables.iter().any(uninhabited),
                None => uninhabited(variable),
            })
    }
}

fn unjoined_report(candidate: &Candidate<'_>, reason: UnjoinedReason) -> UnjoinedPair {
    UnjoinedPair {
        first: Arc::clone(candidate.first),
        second: Arc::clone(candidate.second),
        position: candidate.position.clone(),
        overlap: None,
        sides: None,
        reached: None,
        refused: None,
        reason,
        withdrawn: Vec::new(),
        rewrites_argument: false,
    }
}

fn flatten(predicate: Predicate, into: &mut BTreeSet<Predicate>) {
    match predicate {
        Predicate::True => {}
        Predicate::And(conjuncts) => {
            for conjunct in conjuncts {
                flatten(conjunct, into);
            }
        }
        predicate => {
            into.insert(predicate);
        }
    }
}

/// Run the check on `definition`, which must hold [`ValueClaims::withheld`], classifying the
/// stage-2 pairs `scope` names.
pub(crate) fn check(
    definition: &BackendDefinition,
    scope: CheckScope,
    memo: ConditionMemo,
) -> ValueClaims {
    // The verdict is cached with the definition, so it must not depend on the request that loads
    // it: the check reads no request cancellation and no outer step deadline, only the deadline
    // it arms for each condition (R1.6).
    crate::stop::detached(|| check_detached(definition, scope, memo))
}

/// The executable equations the check reads (every equation of the function theory but the
/// `symbolic` ones), by index and priority as equation selection offers them, and in one list.
fn executable_equations(definition: &BackendDefinition) -> (Groups, Vec<Equation>) {
    let mut groups = Groups::new();
    let mut equations = Vec::new();
    for (index, priorities) in definition.function_theory() {
        for (priority, rules) in priorities {
            for rule in rules {
                if symbolic(rule) && !switches::active().join_with_symbolic {
                    continue;
                }
                groups
                    .entry(index.clone())
                    .or_default()
                    .entry(*priority)
                    .or_default()
                    .push(Arc::clone(rule));
                equations.push(Equation {
                    rule: Arc::clone(rule),
                    index: index.clone(),
                });
            }
        }
    }
    (groups, equations)
}

#[allow(
    clippy::too_many_lines,
    reason = "the check's stages in their order, each a short loop"
)]
fn check_detached(
    definition: &BackendDefinition,
    scope: CheckScope,
    memo: ConditionMemo,
) -> ValueClaims {
    let _span = measure::algorithm_span(measure::Algorithm::BackendConfluenceCheck);
    let _apart = ApartScope::enter();
    let _domain = crate::term::domain::DomainScope::enter(definition);
    let mut checked = Checked::default();
    let (groups, equations) = executable_equations(definition);
    checked.counts.equations = equations.len();

    // P5: one lookup per equation.
    let mut row_seeds = Vec::new();
    for equation in &equations {
        let violation = match &equation.index {
            TermIndex::Symbol(name) => definition.symbols().get(name).and_then(|symbol| {
                (symbol.attributes.head_role() == HeadRole::FreeConstructor)
                    .then(|| ViolationKind::ConstructorHeaded(name.clone()))
            }),
            TermIndex::Injection => Some(ViolationKind::InjectionHeaded),
            index @ (TermIndex::Map | TermIndex::List | TermIndex::Set | TermIndex::Variable) => {
                checked.tainted_indexes.insert(index.clone());
                Some(ViolationKind::IndexedAt(index.clone()))
            }
            TermIndex::DomainValue | TermIndex::And => None,
        };
        if let Some(kind) = violation {
            if kind.withdraws() {
                // An equation outside the check's reasoning: its overlaps are never classified,
                // so it is seeded into the closure like a pair that does not join (R1.5).
                row_seeds.push(Arc::clone(&equation.rule));
            }
            checked.violations.push(Violation {
                rule: Some(Arc::clone(&equation.rule)),
                kind,
            });
        }
    }
    // Per-equation reports: equations the evaluator never applies as written. Each describes one
    // axiom against the evaluator, whatever claims the definition makes, so the walk runs before
    // the check decides whether any claim can be withdrawn; where claims exist, the reported
    // equations are also seeded into the closure like pairs that do not join.
    let mut unjoined = equations
        .iter()
        .filter_map(|equation| {
            let reason = if equation
                .rule
                .computed_attributes
                .unbound_result_variables
                .is_empty()
            {
                computed_below_root(&equation.rule.lhs).map(UnjoinedReason::ComputedBelowRoot)?
            } else {
                UnjoinedReason::UnboundResultVariables
            };
            Some(UnjoinedPair {
                first: Arc::clone(&equation.rule),
                second: Arc::clone(&equation.rule),
                position: Vec::new(),
                overlap: None,
                sides: None,
                reached: None,
                refused: None,
                reason,
                withdrawn: Vec::new(),
                rewrites_argument: false,
            })
        })
        .collect::<Vec<_>>();

    let withdrawable = definition
        .symbols()
        .values()
        .any(|symbol| closure::taintable(symbol) && certified_root(definition, symbol));
    if !withdrawable {
        // No symbol the gate is asked about (`certified_root`, the union of the sites' symbol
        // classes) can be tainted by any closure (`closure::taintable`): there is no
        // equation head, hooked or not, and every overloaded symbol is a free constructor or
        // hooked. So no pair changes a claim, and the collection claims read only equations
        // indexed at a collection or a bare variable, which the rows above taint.
        checked.counts.unjoined = unjoined.len();
        checked.unjoined = unjoined;
        return ValueClaims(Arc::new(Verdict::Checked(Box::new(checked))));
    }

    let mut context = Context {
        definition,
        families: Families::of(definition),
        sorts: symbols::Sorts::of(definition),
        groups,
        renamed: FxHashMap::default(),
        memo: (memo == ConditionMemo::On && !switches::active().no_condition_memo)
            .then(memo::Memo::default),
        fresh: 0,
        counts: CheckCounts::default(),
    };
    context.counts.equations = checked.counts.equations;
    context.counts.families = context.families.len();

    // P5 rows of the overload families.
    let mut family_violations = vec![false; context.families.len()];
    for equation in &equations {
        let TermIndex::Symbol(name) = &equation.index else {
            continue;
        };
        let Some(family) = context.families.family(name) else {
            continue;
        };
        if definition.overloads().overloaded_by(name).is_empty() {
            continue;
        }
        if overload_equation(definition, &equation.rule).is_none()
            && is_overload_like(definition, &equation.rule)
        {
            family_violations[family] = true;
            checked.violations.push(Violation {
                rule: Some(Arc::clone(&equation.rule)),
                kind: ViolationKind::OverloadShape(name.clone()),
            });
        }
    }
    for (family, violated) in family_violations.iter_mut().enumerate() {
        let members = context.families.members(family).to_vec();
        for (index, left) in members.iter().enumerate() {
            for right in &members[index + 1..] {
                let common = definition.overloads().common_overloads(left, right);
                if common.is_empty()
                    || definition.overloads().is_overloading(left, right)
                    || definition.overloads().is_overloading(right, left)
                {
                    continue;
                }
                let minimal = common
                    .iter()
                    .filter(|candidate| {
                        !common.iter().any(|other| {
                            other != *candidate
                                && definition.overloads().is_overloading(candidate, other)
                        })
                    })
                    .count();
                if minimal != 1 {
                    *violated = true;
                    checked.violations.push(Violation {
                        rule: None,
                        kind: ViolationKind::NoLeastCommonOverload(left.clone(), right.clone()),
                    });
                }
            }
        }
    }

    // Self pairs: an equation whose left-hand side matches one subject in several ways is a
    // root peak with itself (R2.2). It joins when its right-hand side and `ensures` read only
    // variables every matching gives the same value; otherwise it is not shown to join.
    for equation in &equations {
        if switches::active().drop_several_matches {
            break;
        }
        let undetermined = undetermined_variables(&equation.rule.lhs);
        if undetermined.is_empty() {
            continue;
        }
        context.counts.several_matches += 1;
        context.counts.overlaps += 1;
        let read = match &equation.rule.rhs {
            RuleRhs::Term(term) => Some(term.attributes().variables.to_btree_set()),
            RuleRhs::Bottom => Some(BTreeSet::new()),
            RuleRhs::Disjunction(_) | RuleRhs::Top | RuleRhs::Predicates(_)
                if switches::active().self_pair_reads_opaque_rhs_as_nothing =>
            {
                Some(BTreeSet::new())
            }
            // A right-hand side the check does not read: count it as reading every variable.
            RuleRhs::Disjunction(_) | RuleRhs::Top | RuleRhs::Predicates(_) => None,
        }
        .map(|mut read| {
            if !switches::active().self_pair_ignores_ensures {
                for predicate in equation.rule.ensures.iter() {
                    read.extend(predicate.free_variables());
                }
            }
            read
        });
        if read.is_some_and(|read| read.is_disjoint(&undetermined)) {
            context.counts.joined += 1;
            continue;
        }
        unjoined.push(UnjoinedPair {
            first: Arc::clone(&equation.rule),
            second: Arc::clone(&equation.rule),
            position: Vec::new(),
            overlap: None,
            sides: None,
            reached: None,
            refused: None,
            reason: UnjoinedReason::Unresolved(UnresolvedShape::SeveralMatches),
            withdrawn: Vec::new(),
            rewrites_argument: false,
        });
    }

    // Stage 1: the root pairs at the members of each family, without lifting.
    let mut stage_one = vec![true; context.families.len()];
    let root_groups = context
        .groups
        .iter()
        .flat_map(|(index, priorities)| {
            let family = match index {
                TermIndex::Symbol(name) => context.families.family(name),
                _ => None,
            };
            priorities
                .values()
                .map(move |rules| (family, rules.clone()))
        })
        .collect::<Vec<_>>();
    for (family, rules) in &root_groups {
        let Some(family) = *family else {
            continue;
        };
        for (position, first) in rules.iter().enumerate() {
            for second in &rules[position + 1..] {
                let candidate = Candidate {
                    first,
                    second,
                    position: Vec::new(),
                    lifting: false,
                };
                if let Classified::NotJoined(pair) = context.classify(&candidate) {
                    stage_one[family] = false;
                    unjoined.push(*pair);
                }
            }
        }
    }
    for (family, (joined, violated)) in stage_one.iter().zip(&family_violations).enumerate() {
        if *joined && !violated {
            context.families.set_confluent(family);
            context.counts.confluent_families += 1;
        }
    }

    // Stage 2: every other root pair, and every inner pair, of which `Gate` classifies those
    // with a relevant equation (`CheckScope::Gate`).
    let mut closure = closure::Closure::new(definition, &context.sorts, &equations);
    let relevant = closure.relevant(&|symbol| gate_symbol(definition, symbol));
    context.counts.relevant_equations = relevant.iter().filter(|relevant| **relevant).count();
    let needs_both = switches::active().relevance_needs_both;
    let classified = |first: &Arc<RewriteRule>, second: &Arc<RewriteRule>| {
        let relevant = |rule| relevant[closure.id(rule)];
        scope == CheckScope::All
            || if needs_both {
                relevant(first) && relevant(second)
            } else {
                relevant(first) || relevant(second)
            }
    };
    for (family, rules) in &root_groups {
        if family.is_some() {
            continue;
        }
        for (position, first) in rules.iter().enumerate() {
            for second in &rules[position + 1..] {
                if !classified(first, second) {
                    context.counts.skipped += 1;
                    continue;
                }
                let candidate = Candidate {
                    first,
                    second,
                    position: Vec::new(),
                    lifting: true,
                };
                if let Classified::NotJoined(pair) = context.classify(&candidate) {
                    unjoined.push(*pair);
                }
            }
        }
    }
    let switches = switches::active();
    for equation in &equations {
        if switches.drop_inner_positions {
            break;
        }
        for (position, subterm) in inner_positions(&equation.rule.lhs) {
            let index = term_index(&subterm);
            for second in context.candidates(&index) {
                if switches.separate_inner_by_priority
                    && second.attributes.priority != equation.rule.attributes.priority
                {
                    continue;
                }
                // A pair at an argument whose second equation is rooted at a symbol a gate site
                // is asked about (an equation head or an overloaded symbol) is reported whatever
                // its relevance (`UnjoinedPair::in_argument`), so it is classified under every
                // scope. Such an equation's closure reaches its own root, so the pair is relevant
                // too; the disjunct states the class instead of relying on that.
                let rewrites_argument = argument_position(&equation.rule.lhs, &position)
                    && matches!(
                        term_index(&second.lhs),
                        TermIndex::Symbol(name) if gate_symbol(definition, &name)
                    );
                if !classified(&equation.rule, &second) && !rewrites_argument {
                    context.counts.skipped += 1;
                    continue;
                }
                let candidate = Candidate {
                    first: &equation.rule,
                    second: &second,
                    position: position.clone(),
                    lifting: true,
                };
                if let Classified::NotJoined(mut pair) = context.classify(&candidate) {
                    pair.rewrites_argument = rewrites_argument;
                    unjoined.push(*pair);
                }
            }
        }
    }

    checked.counts = context.counts;
    checked.counts.unjoined = unjoined.len();
    debug_assert_eq!(
        checked.counts.simplifier_calls,
        checked.counts.condition_memo_hits
            + checked.counts.key_simplifications
            + checked.counts.as_written_simplifications,
        "every condition is answered from the memo, through its key or as written"
    );
    #[cfg(test)]
    {
        checked.families = Some(context.families.clone());
    }
    let mut pinned_heads = BTreeSet::new();
    for (symbol, heads) in closure.pinned_heads() {
        checked.violations.push(Violation {
            rule: None,
            kind: ViolationKind::PinnedByInjectiveTotal(symbol),
        });
        pinned_heads.extend(heads);
    }
    for pair in &mut unjoined {
        pair.spell_canonically();
        pair.withdrawn = closure
            .taint([&pair.first, &pair.second], [])
            .into_iter()
            .filter(|symbol| gate_symbol(definition, symbol))
            .collect();
    }
    let tainted = closure.taint(
        unjoined
            .iter()
            .flat_map(|pair| [&pair.first, &pair.second])
            .chain(&row_seeds),
        pinned_heads,
    );
    debug_assert!(
        switches::active().seed_heads_only
            || tainted.iter().all(|name| definition
                .symbols()
                .get(name)
                .is_some_and(|symbol| closure::taintable(symbol))),
        "the closure tainted a symbol outside `taintable`, which the shortcut reads: {tainted:?}"
    );
    for symbol in &tainted {
        checked
            .tainted_indexes
            .insert(TermIndex::Symbol(symbol.clone()));
    }
    checked.tainted_symbols = tainted;
    checked.unjoined = unjoined;
    ValueClaims(Arc::new(Verdict::Checked(Box::new(checked))))
}

/// The lesser production an overload equation of `rule`'s greater root lowers to, when `rule`
/// has the shape `g(inj(x1), ..., inj(xn)) = inj(h(x1, ..., xn))` (each injection possibly the
/// identity) with `h` a lesser production of `g`.
fn overload_equation(definition: &BackendDefinition, rule: &RewriteRule) -> Option<Name> {
    let TermKind::Application {
        symbol: greater,
        arguments,
        ..
    } = rule.lhs.kind()
    else {
        return None;
    };
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return None;
    };
    let application = match rhs.kind() {
        TermKind::Injection { term, .. } => term,
        _ => rhs,
    };
    let TermKind::Application {
        symbol: lesser,
        arguments: lesser_arguments,
        ..
    } = application.kind()
    else {
        return None;
    };
    if !definition
        .overloads()
        .is_overloading(&greater.name, &lesser.name)
        || arguments.len() != lesser_arguments.len()
        || !rule.requires.is_empty()
    {
        return None;
    }
    let operand = |term: &Term| match term.kind() {
        TermKind::Injection { term, .. } => term.clone(),
        _ => term.clone(),
    };
    arguments
        .iter()
        .zip(lesser_arguments)
        .all(|(argument, lesser_argument)| {
            matches!(operand(argument).kind(), TermKind::Variable(_))
                && operand(argument) == *lesser_argument
        })
        .then(|| lesser.name.clone())
}

/// Whether `rule` lowers its greater root to a lesser production of it, whatever its shape: the
/// equations P5's shape row is about.
fn is_overload_like(definition: &BackendDefinition, rule: &RewriteRule) -> bool {
    let (
        TermKind::Application {
            symbol: greater, ..
        },
        RuleRhs::Term(rhs),
    ) = (rule.lhs.kind(), &rule.rhs)
    else {
        return false;
    };
    let application = match rhs.kind() {
        TermKind::Injection { term, .. } => term,
        _ => rhs,
    };
    matches!(application.kind(), TermKind::Application { symbol, .. }
        if definition.overloads().is_overloading(&greater.name, &symbol.name))
}
