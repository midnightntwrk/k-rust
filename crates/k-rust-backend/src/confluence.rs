//! ```toml algorithm
//! id = "backend.confluence.critical_pairs"
//! name = "load-time critical-pair check by order-sorted unification and an innermost join"
//! sites = ["check", "Context::classify", "Context::conditions"]
//! variable = "e = executable equations; p = candidate pairs: the pairs of one index and priority group, and the inner positions of each left-hand side times the equations offered at its index and family; b = unifier branch states of one pair (at most UNIFIER_BRANCHES, 4,096); c = cases of one join (at most JOIN_CASES, 64); s = steps of one side (at most JOIN_STEPS, 32); t = term size"
//! counters = ["ConfluencePairs", "ConfluenceUnifierBranches", "ConfluenceJoinSteps", "ConfluenceSimplifierCalls"]
//! span = "per call"
//!
//! [[cost]]
//! mode = "one definition (check)"
//! bound = "one pass over the e equations for the rows of the constructor and overload preconditions; nothing more when no equation head is declared; otherwise, for the self pairs of left-hand sides that may match one subject in several ways, one fixpoint per equation over its left-hand side's positions of at most as many rounds as it has variables, then p unifications of at most b branch states each, every branch step one substitution of O(t); per overlap one predicate simplification of the two requires and a join of at most c cases, each normalizing two sides by at most s steps, every step one match against each equation offered at the redex and one unification per equation not shown to apply; then one closure pass per non-joined pair and one over all of them, each visiting an equation once and pushing a symbol once, with one memoized sort-reach walk per variable sort"
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
//!    overload axioms of confluent families (`unify.rs`);
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
//! definition holds [`ValueClaims::withheld`], which admits no claim, so that no claim the check
//! is about to withdraw can contribute to its own verdict (a `requires` refuted through a claim,
//! a join step through a certified root). Every place that mints a claim asks
//! [`ValueClaims::admit`] for the index of the term it vouches for.

mod closure;
mod conditions;
mod join;
pub(crate) mod switches;
pub(crate) mod symbols;
#[cfg(test)]
mod tests;
mod unify;

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use rustc_hash::FxHashSet;

use k_rust_kore::measure::{self, Counter};

pub(crate) use join::SettledRoot;
pub use unify::UnresolvedShape;

use crate::{
    definition::BackendDefinition,
    rule::{
        ApartScope, Concreteness, ConstraintKind, Predicate, RewriteRule, RuleRhs, TermIndex,
        rename_apart, term_index,
    },
    simplify::{SimplificationOptions, simplify_predicate_with_solver},
    smt::NoSolver,
    substitution::{Substitution, substitute},
    term::{HeadRole, Name, Sort, Term, TermKind, Variable},
};
use unify::{Families, Unifier, computed};

/// The verdict of the load-time check: which term indexes may carry value claims, and the pairs
/// that withdrew the others. Cheap to clone.
#[derive(Clone, Debug)]
pub struct ValueClaims(Arc<Verdict>);

#[derive(Debug)]
enum Verdict {
    /// The check has not run, or is running: no claim is admitted.
    Withheld,
    Checked(Box<Checked>),
}

#[derive(Debug, Default)]
struct Checked {
    tainted_symbols: BTreeSet<Name>,
    tainted_indexes: FxHashSet<TermIndex>,
    unjoined: Vec<UnjoinedPair>,
    violations: Vec<Violation>,
    counts: CheckCounts,
    /// Test builds: the overload families, with stage 1's verdicts.
    #[cfg(test)]
    families: Option<Families>,
}

/// The constructions of a value claim that ask the gate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum GateSite {
    /// The instance-normal scan of an equation-head application.
    EquationHead,
    /// The instance-normal scan of a collection.
    Collection,
    /// The simplifier's normal-form certificate.
    Certificate,
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
    #[must_use]
    pub(crate) fn admit_at(&self, index: &TermIndex, site: GateSite) -> Option<UntaintedIndex> {
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
    /// Calls of the predicate simplifier (conditions refuted or decided).
    pub simplifier_calls: usize,
    /// Equations whose left-hand side may match one subject in several ways (a map or set
    /// pattern with an entry the rest of the left-hand side does not fix): each is a root pair
    /// with itself, counted among the overlaps and as joined or not joined.
    pub several_matches: usize,
    /// Overload families, and those found confluent by stage 1.
    pub families: usize,
    pub confluent_families: usize,
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
    /// The equation heads the taint closure of this pair alone withdraws, sorted: empty when the
    /// pair constrains no equation head, so that it changes no claim.
    pub withdrawn: Vec<Name>,
}

impl UnjoinedPair {
    /// Whether the pair withdraws a value claim: the pairs the backend reports.
    #[must_use]
    pub fn relevant(&self) -> bool {
        !self.withdrawn.is_empty()
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
    /// uninterpreted symbol below its root: the evaluator never applies it to normal-form
    /// arguments, yet it is an axiom.
    ComputedBelowRoot(Name),
    /// A right-hand side the join does not read (a disjunction, `\top` or predicates).
    UnsupportedRightHandSide,
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
fn collapse_conjunctions(pattern: &Term) -> Term {
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
        .difference(&determined)
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

/// The state of one check.
pub(crate) struct Context<'d> {
    definition: &'d BackendDefinition,
    families: Families,
    /// The sorts that may have a normal form, and those with an element in every model
    /// (`symbols.rs`).
    sorts: symbols::Sorts,
    /// The executable equations, by index and priority, as equation selection offers them.
    groups: BTreeMap<TermIndex, BTreeMap<u8, Vec<Arc<RewriteRule>>>>,
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
    fn simplify(&mut self, predicate: Predicate) -> Option<Predicate> {
        self.counts.simplifier_calls += 1;
        measure::bump(Counter::ConfluenceSimplifierCalls);
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
        let second = match rename_apart(candidate.second, &first.computed_attributes.variables, &[])
        {
            Some((renamed, _)) if !switches::active().no_rename_apart => Arc::new(renamed),
            _ => Arc::clone(candidate.second),
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
            && self
                .definition
                .sort_graph()
                .check_subsort(&second_sort, &inner_sort)
                != Ok(true)
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
                        format!("VarOverlapStep{}!unify", self.fresh),
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

/// Run the check on `definition`, which must hold [`ValueClaims::withheld`].
pub(crate) fn check(definition: &BackendDefinition) -> ValueClaims {
    // The verdict is cached with the definition, so it must not depend on the request that loads
    // it: the check reads no request cancellation and no outer step deadline, only the deadline
    // it arms for each condition (R1.6).
    crate::stop::detached(|| check_detached(definition))
}

fn check_detached(definition: &BackendDefinition) -> ValueClaims {
    let _span = measure::algorithm_span(measure::Algorithm::BackendConfluenceCheck);
    let _apart = ApartScope::enter();
    let mut checked = Checked::default();
    let mut groups = BTreeMap::<TermIndex, BTreeMap<u8, Vec<Arc<RewriteRule>>>>::new();
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
            if matches!(
                kind,
                ViolationKind::ConstructorHeaded(_) | ViolationKind::InjectionHeaded
            ) {
                // An equation outside the check's reasoning: seeded into the closure like a pair
                // that does not join (R1.5).
                row_seeds.push(Arc::clone(&equation.rule));
            }
            checked.violations.push(Violation {
                rule: Some(Arc::clone(&equation.rule)),
                kind,
            });
        }
    }
    let heads = definition
        .symbols()
        .values()
        .any(|symbol| symbol.attributes.head_role() == HeadRole::EquationHead);
    if !heads {
        // No claim is about an equation-head application, and the collection claims read only
        // equations indexed at a collection or a bare variable, which the rows above taint.
        return ValueClaims(Arc::new(Verdict::Checked(Box::new(checked))));
    }

    let mut context = Context {
        definition,
        families: Families::of(definition),
        sorts: symbols::Sorts::of(definition),
        groups,
        fresh: 0,
        counts: CheckCounts::default(),
    };
    context.counts.equations = checked.counts.equations;
    context.counts.families = context.families.len();
    let mut unjoined = Vec::new();

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

    // Per-equation reports: equations the evaluator never applies as written.
    for equation in &equations {
        let reason = if !equation
            .rule
            .computed_attributes
            .unbound_result_variables
            .is_empty()
        {
            Some(UnjoinedReason::UnboundResultVariables)
        } else {
            computed_below_root(&equation.rule.lhs).map(UnjoinedReason::ComputedBelowRoot)
        };
        if let Some(reason) = reason {
            unjoined.push(UnjoinedPair {
                first: Arc::clone(&equation.rule),
                second: Arc::clone(&equation.rule),
                position: Vec::new(),
                overlap: None,
                sides: None,
                reached: None,
                refused: None,
                reason,
                withdrawn: Vec::new(),
            });
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
            RuleRhs::Term(term) => Some(term.attributes().variables.clone()),
            RuleRhs::Bottom => Some(BTreeSet::new()),
            // A right-hand side the check does not read: count it as reading every variable.
            RuleRhs::Disjunction(_) | RuleRhs::Top | RuleRhs::Predicates(_) => None,
        }
        .map(|mut read| {
            for predicate in equation.rule.ensures.iter() {
                read.extend(predicate.free_variables());
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

    // Stage 2: every other root pair, and every inner pair.
    for (family, rules) in &root_groups {
        if family.is_some() {
            continue;
        }
        for (position, first) in rules.iter().enumerate() {
            for second in &rules[position + 1..] {
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
                let candidate = Candidate {
                    first: &equation.rule,
                    second: &second,
                    position: position.clone(),
                    lifting: true,
                };
                if let Classified::NotJoined(pair) = context.classify(&candidate) {
                    unjoined.push(*pair);
                }
            }
        }
    }

    checked.counts = context.counts;
    checked.counts.unjoined = unjoined.len();
    #[cfg(test)]
    {
        checked.families = Some(context.families.clone());
    }
    let mut closure = closure::Closure::new(definition, &context.sorts, &equations);
    let is_head = |symbol: &Name| {
        definition
            .symbols()
            .get(symbol)
            .is_some_and(|symbol| symbol.attributes.head_role() == HeadRole::EquationHead)
    };
    let mut pinned_heads = BTreeSet::new();
    for (symbol, heads) in closure.pinned_heads() {
        checked.violations.push(Violation {
            rule: None,
            kind: ViolationKind::PinnedByInjectiveTotal(symbol),
        });
        pinned_heads.extend(heads);
    }
    for pair in &mut unjoined {
        pair.withdrawn = closure
            .taint([&pair.first, &pair.second], [])
            .into_iter()
            .filter(|symbol| is_head(symbol))
            .collect();
    }
    let tainted = closure.taint(
        unjoined
            .iter()
            .flat_map(|pair| [&pair.first, &pair.second])
            .chain(&row_seeds),
        pinned_heads,
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
