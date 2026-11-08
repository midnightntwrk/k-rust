//! The static may-follow graph of a definition's authored rewrite rules ([`may_follow`]), the
//! universe of kink-flow's rule windows.
//!
//! A window is a sequence of rewrite rules some path takes as consecutive committed steps
//! (k-rust `coverage.windows`). Rule `B` may follow rule `A` when `A`'s right-hand side unifies
//! with `B`'s left-hand side, every function application, builtin-domain value, collection and
//! conjunction read as a fresh variable and each variable occurrence as its own: syntactic
//! first-order unification over the free constructors and cells of the two internalized
//! configurations, looking through injections. Conditions are not read.
//!
//! This over-approximates the steps that can follow. The successor of a step of `A` is the
//! normal form of an instance of `A`'s right-hand side; normalization evaluates function
//! applications and leaves every free constructor in place, so wherever the right-hand side has
//! a free constructor along a path of free constructors from its root, so does the successor.
//! `B` applies to the successor only if its left-hand side matches it, which requires the same
//! constructor wherever both have one, and a value of a variable's sort wherever one side has a
//! variable and the other a constructor (a value whose head is a free constructor has that
//! constructor's result sort). Every subterm read as a variable can stand for anything, so a
//! mismatch that only an abstracted subterm could hide is never claimed, and reading each
//! occurrence of a variable apart only drops constraints. A `K` sequence whose first element is
//! a `K`-sorted variable or computed term is read as a fresh variable too: such an element can
//! be the empty sequence or several items, which shifts every later element.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust::names::{BuiltinSort, WellKnownSymbol};
use k_rust_backend::{
    definition::BackendDefinition,
    matching::SortGraph,
    rule::RuleRhs,
    term::{HeadRole, Sort, Symbol, Term, TermKind, Variable},
};
use kink_patch::SentenceRef;

use super::{Authorship, RuleAuthors};

/// The may-follow graph of a definition's authored rewrite rules (module documentation): each
/// sentence behind a rewrite rule that is neither unattributed nor a heating or cooling rule,
/// and, per such sentence, the sentences whose rules may take the next step after one of its
/// rules.
#[derive(Clone, Debug, Default)]
pub struct MayFollow {
    /// Per sentence, its rules' left-hand sides and right-hand side alternatives, in the
    /// definition's order (`None`: a right-hand side that is no term, read as anything).
    rules: BTreeMap<SentenceRef, Vec<Sides>>,
    edges: BTreeMap<SentenceRef, BTreeSet<SentenceRef>>,
    /// Per edge, the first right-hand side of the source and left-hand side of the target that
    /// unify, in the definition's order: the pair [`MayFollow::unified`] builds the pattern of.
    witnesses: BTreeMap<(SentenceRef, SentenceRef), (Option<Term>, Term)>,
}

#[derive(Clone, Debug)]
struct Sides {
    lhs: Term,
    rhs: Vec<Option<Term>>,
}

/// An empty successor set.
static NONE: BTreeSet<SentenceRef> = BTreeSet::new();

impl MayFollow {
    /// The authored rewrite rule sentences, in sentence order.
    pub fn sentences(&self) -> impl Iterator<Item = &SentenceRef> {
        self.rules.keys()
    }

    /// The sentences whose rules may follow a step of `at`'s.
    #[must_use]
    pub fn successors(&self, at: &SentenceRef) -> &BTreeSet<SentenceRef> {
        self.edges.get(at).unwrap_or(&NONE)
    }

    /// The number of edges.
    #[must_use]
    pub fn edges(&self) -> usize {
        self.edges.values().map(BTreeSet::len).sum()
    }

    /// The configuration a step of `from` can leave that a rule of `to` can match, as a KORE
    /// pattern: the unifier of the first right-hand side of `from` and left-hand side of `to`
    /// that unify ([`MayFollow::successors`]), with every abstracted subterm and every variable a
    /// fresh variable of its sort (`VarW0`, `VarW1`, ... in the order written), so the pattern
    /// holds free constructors, cells, injections and variables only. Where one side has a
    /// constructor and the other a variable or an abstracted subterm, the constructor's side is
    /// taken. `None` where `to` does not follow `from`.
    #[must_use]
    pub fn unified(
        &self,
        from: &SentenceRef,
        to: &SentenceRef,
    ) -> Option<k_rust::kore::ast::Pattern> {
        let (rhs, lhs) = self.witnesses.get(&(from.clone(), to.clone()))?;
        let mut fresh = 0;
        let term = match rhs {
            Some(rhs) => meet(rhs, lhs, &mut fresh),
            None => sanitized(lhs, &mut fresh),
        };
        Some(k_rust_backend::externalize::term(&term))
    }
}

/// The may-follow graph of `definition`'s rewrite rules (module documentation), each rule by the
/// baseline sentences `authors` names for it. A rule whose id has no baseline sentence, and a
/// heating or cooling rule ([`RuleAuthors::strictness_ids`]), is no node: its sentence is no
/// authored rule. A sentence behind several rules (a disjunctive left-hand side) has the
/// alternatives of all of them, and follows, or is followed by, another where some pair unifies.
#[must_use]
pub fn may_follow(definition: &BackendDefinition, authors: &RuleAuthors) -> MayFollow {
    let strictness = authors.strictness_ids();
    let mut rules = BTreeMap::<SentenceRef, Vec<Sides>>::new();
    for rule in definition
        .rewrite_theory()
        .values()
        .flat_map(|priorities| priorities.values())
        .flatten()
    {
        let rule = &rule.rule;
        let id = &rule.attributes.unique_id;
        let Some(Authorship::Sentences(sentences)) = authors.get(id) else {
            continue;
        };
        if strictness.contains(id.as_str()) {
            continue;
        }
        let rhs = match &rule.rhs {
            RuleRhs::Term(term) => vec![Some(term.clone())],
            RuleRhs::Disjunction(alternatives) => alternatives
                .iter()
                .map(|alternative| Some(alternative.term.clone()))
                .collect(),
            RuleRhs::Bottom => Vec::new(),
            RuleRhs::Top | RuleRhs::Predicates(_) => vec![None],
        };
        for sentence in sentences {
            rules.entry(sentence.clone()).or_default().push(Sides {
                lhs: rule.lhs.clone(),
                rhs: rhs.clone(),
            });
        }
    }
    let graph = definition.sort_graph();
    let mut edges = BTreeMap::<SentenceRef, BTreeSet<SentenceRef>>::new();
    let mut witnesses = BTreeMap::new();
    for (from, from_sides) in &rules {
        for (to, to_sides) in &rules {
            let witness = from_sides.iter().find_map(|source| {
                source.rhs.iter().find_map(|rhs| {
                    to_sides.iter().find_map(|target| {
                        rhs.as_ref()
                            .is_none_or(|rhs| unifies(rhs, &target.lhs, graph))
                            .then(|| (rhs.clone(), target.lhs.clone()))
                    })
                })
            });
            if let Some(witness) = witness {
                edges.entry(from.clone()).or_default().insert(to.clone());
                witnesses.insert((from.clone(), to.clone()), witness);
            }
        }
    }
    MayFollow {
        rules,
        edges,
        witnesses,
    }
}

/// A term as the unification reads it, through its injections.
enum Shape<'t> {
    /// A variable of its sort.
    Variable(&'t Sort),
    /// A subterm read as a fresh variable.
    Abstracted,
    /// An application of a free constructor.
    Constructor(&'t Arc<Symbol>, &'t [Term]),
}

/// The term below `term`'s injections.
fn uninjected(mut term: &Term) -> &Term {
    while let TermKind::Injection { term: inner, .. } = term.kind() {
        term = inner;
    }
    term
}

/// Whether `symbol`'s applications are free: a constructor (or sort injection) with no hook, no
/// collection role and no axiom that identifies applications.
fn free(symbol: &Symbol) -> bool {
    symbol.attributes.head_role() == HeadRole::FreeConstructor
        && symbol.attributes.hook.is_none()
        && symbol.attributes.collection.is_none()
}

fn shape(term: &Term) -> Shape<'_> {
    let term = uninjected(term);
    match term.kind() {
        TermKind::Variable(variable) => Shape::Variable(&variable.sort),
        TermKind::Application {
            symbol, arguments, ..
        } if free(symbol) => {
            // A sequence whose first element is a whole `K`, not one item, can be empty or
            // several items: its later elements have no fixed place.
            if symbol.is(WellKnownSymbol::KSeq)
                && let Some(first) = arguments.first()
                && !matches!(shape(first), Shape::Constructor(..))
                && first.sort().is_builtin(BuiltinSort::K)
            {
                return Shape::Abstracted;
            }
            Shape::Constructor(symbol, arguments)
        }
        _ => Shape::Abstracted,
    }
}

/// Whether a value of a free constructor `symbol`'s result sort may be a value of `sort`: unless
/// the sort graph says it is not below.
fn may_be_of(symbol: &Symbol, sort: &Sort, graph: &SortGraph) -> bool {
    graph.check_subsort(&symbol.result_sort, sort) != Ok(false)
}

/// Whether `left` and `right` unify under the abstraction (module documentation).
fn unifies(left: &Term, right: &Term, graph: &SortGraph) -> bool {
    let mut work = vec![(left, right)];
    while let Some((left, right)) = work.pop() {
        match (shape(left), shape(right)) {
            (Shape::Constructor(f, xs), Shape::Constructor(g, ys)) => {
                if f.name != g.name || xs.len() != ys.len() {
                    return false;
                }
                work.extend(xs.iter().zip(ys));
            }
            (Shape::Variable(sort), Shape::Constructor(symbol, _))
            | (Shape::Constructor(symbol, _), Shape::Variable(sort))
                if !may_be_of(symbol, sort, graph) =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
}

/// A fresh variable of `sort`, the next of `fresh`.
fn fresh_variable(sort: Sort, fresh: &mut usize) -> Term {
    let variable = Term::variable(Variable::new(format!("VarW{fresh}"), sort));
    *fresh += 1;
    variable
}

/// `term`'s injections around `inner`, outermost first.
fn reinjected(term: &Term, inner: Term) -> Term {
    let mut wrappers = Vec::new();
    let mut current = term;
    while let TermKind::Injection {
        source,
        target,
        term,
    } = current.kind()
    {
        wrappers.push((*source, *target));
        current = term;
    }
    wrappers
        .into_iter()
        .rev()
        .fold(inner, |inner, (source, target)| {
            Term::injection(source, target, inner)
        })
}

/// `term` with every variable and abstracted subterm a fresh variable of its sort. `term` is a
/// side of a rule, whose depth the definition's text bounds, so the recursion is bounded by it.
fn sanitized(term: &Term, fresh: &mut usize) -> Term {
    match shape(term) {
        Shape::Constructor(symbol, arguments) => {
            let TermKind::Application { sort_arguments, .. } = uninjected(term).kind() else {
                unreachable!("a constructor shape is an application")
            };
            let arguments = arguments
                .iter()
                .map(|argument| sanitized(argument, fresh))
                .collect();
            reinjected(
                term,
                Term::application(symbol.clone(), *sort_arguments, arguments),
            )
        }
        Shape::Variable(_) | Shape::Abstracted => fresh_variable(term.sort(), fresh),
    }
}

/// The unifier of `rhs` and `lhs`, which unify (module documentation), with fresh variables;
/// recursive over the sides of two rules, as [`sanitized`] is.
fn meet(rhs: &Term, lhs: &Term, fresh: &mut usize) -> Term {
    match (shape(rhs), shape(lhs)) {
        (Shape::Constructor(..), Shape::Constructor(symbol, arguments)) => {
            let TermKind::Application { sort_arguments, .. } = uninjected(lhs).kind() else {
                unreachable!("a constructor shape is an application")
            };
            let Shape::Constructor(_, sources) = shape(rhs) else {
                unreachable!("matched above")
            };
            let arguments = sources
                .iter()
                .zip(arguments)
                .map(|(source, target)| meet(source, target, fresh))
                .collect();
            reinjected(
                lhs,
                Term::application(symbol.clone(), *sort_arguments, arguments),
            )
        }
        (Shape::Constructor(..), _) => sanitized(rhs, fresh),
        (_, Shape::Constructor(..)) => sanitized(lhs, fresh),
        _ => fresh_variable(lhs.sort(), fresh),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn constructor(name: &str, arguments: Vec<Sort>, result: Sort) -> Arc<Symbol> {
        Arc::new(Symbol::constructor(name, arguments, result))
    }

    fn k() -> Sort {
        Sort::builtin(BuiltinSort::K)
    }

    fn item() -> Sort {
        Sort::builtin(BuiltinSort::KItem)
    }

    /// `kseq(first, rest)`.
    fn kseq(first: Term, rest: Term) -> Term {
        Term::application(
            constructor(WellKnownSymbol::KSeq.as_str(), vec![item(), k()], k()),
            Vec::<Sort>::new(),
            vec![first, rest],
        )
    }

    fn dotk() -> Term {
        Term::application(
            constructor(WellKnownSymbol::DotK.as_str(), Vec::new(), k()),
            Vec::<Sort>::new(),
            Vec::new(),
        )
    }

    /// `inj{Op, KItem}(name())`.
    fn op(name: &str) -> Term {
        let sort = Sort::simple("SortOp");
        Term::injection(
            sort,
            item(),
            Term::application(
                constructor(name, Vec::new(), sort),
                Vec::<Sort>::new(),
                Vec::new(),
            ),
        )
    }

    fn variable(name: &str, sort: Sort) -> Term {
        Term::variable(Variable::new(name, sort))
    }

    /// Different free constructors at one position do not unify, through injections; a variable
    /// unifies with any constructor its sort may hold.
    #[test]
    fn constructors_unify_by_head_and_variables_by_sort() {
        let graph = SortGraph::default();
        let rest = || variable("VarK", k());
        assert!(unifies(
            &kseq(op("a"), rest()),
            &kseq(op("a"), dotk()),
            &graph
        ));
        assert!(!unifies(
            &kseq(op("a"), rest()),
            &kseq(op("b"), rest()),
            &graph
        ));
        assert!(unifies(
            &kseq(variable("VarX", item()), rest()),
            &kseq(op("b"), rest()),
            &graph
        ));
        assert!(!unifies(&kseq(op("a"), dotk()), &dotk(), &graph));
    }

    /// A sequence whose first element is a whole `K` can be empty: `V ~> b ~> .K` with `V` the
    /// empty sequence is `b ~> .K`, which `b ~> .K` matches although `V` and `b`, then `b ~> .K`
    /// and `.K`, would not pair up place by place. Such a sequence is read as a fresh variable.
    #[test]
    fn a_sequence_led_by_a_whole_k_is_abstracted() {
        let graph = SortGraph::default();
        let shifted = kseq(variable("VarV", k()), kseq(op("b"), dotk()));
        assert!(matches!(shape(&shifted), Shape::Abstracted));
        assert!(unifies(&shifted, &kseq(op("b"), dotk()), &graph));
        assert!(matches!(
            shape(&kseq(variable("VarX", item()), dotk())),
            Shape::Constructor(..)
        ));
    }

    /// The unifier takes the constructor's side wherever the other has a variable, and writes
    /// every variable fresh.
    #[test]
    fn the_unifier_takes_the_constructors_and_fresh_variables() {
        let rhs = kseq(op("a"), variable("VarK", k()));
        let lhs = kseq(variable("VarX", item()), variable("VarK", k()));
        let met = meet(&rhs, &lhs, &mut 0);
        assert_eq!(met, kseq(op("a"), variable("VarW0", k())));
    }
}
