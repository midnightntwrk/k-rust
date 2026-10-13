//! Property tests for `backend.fresh.object_language`: `substOne` over generated binder terms
//! with `\and`, maps, lists and sets, checked against an independent model of object-language
//! substitution.
//!
//! The model is a small first-order syntax ([`M`]) with two binders: `lambda(X, B)` binds `X` in
//! `B`, and `let(X, E, B)` binds `X` in `B` only, so its middle argument is outside the scope.
//! Its reference substitution renames every bound variable of the body to a name that cannot
//! occur in the replacement (de Bruijn levels), then replaces the target textually. That result
//! is capture-free by construction, so the backend's result must be alpha-equivalent to it, and
//! its free `KVar`s must be those of the body without the target, plus those of the replacement
//! when the target occurs free.
//!
//! The values of a `KVar` sort are tokens, and `lambda` is a free constructor, so two terms that
//! differ only in a bound name are distinct values. Alpha-equivalence is the right comparison
//! for one result against the reference (every capture-avoiding substitution is a renaming of
//! it), but `\and`, map keys and set elements compare values, so the decisions the function
//! takes there (`\bottom`, or no value) are checked against the reasons that justify them, and
//! an argument that denotes no value must give a result that denotes none, and conversely.
//! `substOne` is a function of the value its arguments denote, so two representations of one
//! value (`\and(T, T)` and `T`) must give the same result; [`and_idempotence`] checks that.
//!
//! Opaque subterms: `num(N)` and `num(g(T))` have an `Int` argument, a sort that cannot contain
//! a `KVar`, so substitution copies them verbatim, `T` included (the `KVar` tokens under `g`
//! are data of an integer computation, not occurrences). A `hole` variable of the expression
//! sort may contain a `KVar`, so a call with one outside `num` stays unevaluated. A collection
//! whose rest is not opaque has an `\and` of two collections as its rest; the model has those
//! too, so substitution reaches every part of a collection.

use std::{cell::RefCell, collections::BTreeSet, sync::Arc};

use proptest::{
    collection::vec,
    prelude::*,
    test_runner::{Config, RngAlgorithm, TestCaseError, TestRng, TestRunner},
};

use super::*;
use crate::term::{CollectionSymbols, ListDefinition, MapDefinition, Symbol, Variable};

const CASES: u32 = 1024;
const NAMES: [&str; 5] = ["x", "y", "z", "y0", "x1"];

/// An object-language expression (every node has the expression sort).
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum M {
    Var(String),
    Lam(String, Box<M>),
    Let(String, Box<M>, Box<M>),
    App(Box<M>, Box<M>),
    And(Box<M>, Box<M>),
    /// `mapE(entries rest)`.
    Map(Vec<(M, M)>, Option<Rest>),
    /// `listE(heads rest tails)`; `tails` is empty without a rest.
    List(Vec<M>, Option<Rest>, Vec<M>),
    /// `setE(elements rest)`.
    Set(Vec<M>, Option<Rest>),
    /// `num(N:Int)`.
    NumVar(String),
    /// `num(g(T))`, `g` a function into `Int`: opaque, copied verbatim.
    NumOf(Box<M>),
    /// A variable of the expression sort: blocks evaluation.
    Hole(String),
}

/// The rest `\and(L, R)` of a collection: two collections of its kind without rests, written
/// as `Map`, `List` or `Set` nodes that stand for the collection itself, not its wrapper.
type Rest = Box<(M, M)>;

fn b(m: M) -> Box<M> {
    Box::new(m)
}

// ---------------------------------------------------------------------------------------------
// The model: free variables, renaming, textual substitution, normal form.

/// The object-language subterms of `m` in a fixed order (not the verbatim argument of
/// `num(g(_))`); [`with_children`] rebuilds `m` from new ones in the same order.
fn children(m: &M) -> Vec<&M> {
    fn rest(rest: &Option<Rest>) -> impl Iterator<Item = &M> {
        rest.iter().flat_map(|rest| [&rest.0, &rest.1])
    }
    match m {
        M::Var(_) | M::NumVar(_) | M::NumOf(_) | M::Hole(_) => Vec::new(),
        M::Lam(_, body) => vec![body],
        M::Let(_, middle, body) => vec![middle, body],
        M::App(left, right) | M::And(left, right) => vec![left, right],
        M::Map(entries, r) => entries
            .iter()
            .flat_map(|(k, v)| [k, v])
            .chain(rest(r))
            .collect(),
        M::List(heads, r, tails) => heads.iter().chain(rest(r)).chain(tails).collect(),
        M::Set(items, r) => items.iter().chain(rest(r)).collect(),
    }
}

fn with_children(m: &M, children: Vec<M>) -> M {
    fn take(it: &mut impl Iterator<Item = M>) -> M {
        it.next().expect("one child per position")
    }
    fn rest(r: &Option<Rest>, it: &mut impl Iterator<Item = M>) -> Option<Rest> {
        r.as_ref().map(|_| Box::new((take(it), take(it))))
    }
    let it = &mut children.into_iter();
    match m {
        M::Var(_) | M::NumVar(_) | M::NumOf(_) | M::Hole(_) => m.clone(),
        M::Lam(name, _) => M::Lam(name.clone(), b(take(it))),
        M::Let(name, _, _) => M::Let(name.clone(), b(take(it)), b(take(it))),
        M::App(..) => M::App(b(take(it)), b(take(it))),
        M::And(..) => M::And(b(take(it)), b(take(it))),
        M::Map(entries, r) => {
            let entries = entries.iter().map(|_| (take(it), take(it))).collect();
            M::Map(entries, rest(r, it))
        }
        M::List(heads, r, tails) => {
            let heads = heads.iter().map(|_| take(it)).collect();
            let r = rest(r, it);
            M::List(heads, r, tails.iter().map(|_| take(it)).collect())
        }
        M::Set(items, r) => {
            let items = items.iter().map(|_| take(it)).collect();
            M::Set(items, rest(r, it))
        }
    }
}

fn map_children(m: &M, f: &mut dyn FnMut(&M) -> M) -> M {
    with_children(m, children(m).into_iter().map(f).collect())
}

fn free_vars(m: &M, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
    match m {
        M::Var(name) => {
            if !bound.contains(name) {
                out.insert(name.clone());
            }
        }
        M::Lam(name, body) => {
            bound.push(name.clone());
            free_vars(body, bound, out);
            bound.pop();
        }
        M::Let(name, middle, body) => {
            free_vars(middle, bound, out);
            bound.push(name.clone());
            free_vars(body, bound, out);
            bound.pop();
        }
        _ => {
            for child in children(m) {
                free_vars(child, bound, out);
            }
        }
    }
}

fn fv(m: &M) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    free_vars(m, &mut Vec::new(), &mut out);
    out
}

/// Whether `m` has an occurrence `Var(name)`, bound or free.
fn mentions(m: &M, name: &str) -> bool {
    matches!(m, M::Var(n) if n == name) || children(m).into_iter().any(|c| mentions(c, name))
}

fn any_node(m: &M, test: &dyn Fn(&M) -> bool) -> bool {
    test(m) || children(m).into_iter().any(|c| any_node(c, test))
}

fn binder_names(m: &M, out: &mut BTreeSet<String>) {
    if let M::Lam(name, _) | M::Let(name, _, _) = m {
        out.insert(name.clone());
    }
    for child in children(m) {
        binder_names(child, out);
    }
}

fn rest_of(m: &M) -> Option<&Rest> {
    match m {
        M::Map(_, rest) | M::List(_, rest, _) | M::Set(_, rest) => rest.as_ref(),
        _ => None,
    }
}

/// Renames every binder to `{prefix}{depth}`: an alpha-renaming, because two binders on one
/// path have different depths. A prefix that no generated name has keeps the new names apart
/// from every free name.
fn level_rename(m: &M, prefix: &str, scope: &mut Vec<(String, String)>) -> M {
    let bind = |name: &String, body: &M, scope: &mut Vec<(String, String)>| {
        let new = format!("{prefix}{}", scope.len());
        scope.push((name.clone(), new.clone()));
        let body = level_rename(body, prefix, scope);
        scope.pop();
        (new, b(body))
    };
    match m {
        M::Var(name) => M::Var(
            scope
                .iter()
                .rev()
                .find(|(old, _)| old == name)
                .map_or_else(|| name.clone(), |(_, new)| new.clone()),
        ),
        M::Lam(name, body) => {
            let (new, body) = bind(name, body, scope);
            M::Lam(new, body)
        }
        M::Let(name, middle, body) => {
            let middle = b(level_rename(middle, prefix, scope));
            let (new, body) = bind(name, body, scope);
            M::Let(new, middle, body)
        }
        _ => map_children(m, &mut |c| level_rename(c, prefix, scope)),
    }
}

/// Textual substitution: no binder test, so it is correct only when no binder of `m` is named
/// `target` or a free name of `replacement` (true after `level_rename`).
fn textual(m: &M, target: &str, replacement: &M) -> M {
    match m {
        M::Var(name) if name == target => replacement.clone(),
        _ => map_children(m, &mut |c| textual(c, target, replacement)),
    }
}

/// Maps and sets are unordered: sort their entries, everywhere (also under `num(g(_))`).
fn sorted(m: &M) -> M {
    match map_children(m, &mut sorted) {
        M::NumOf(inner) => M::NumOf(b(sorted(&inner))),
        M::Map(mut entries, rest) => {
            entries.sort();
            M::Map(entries, rest)
        }
        M::Set(mut items, rest) => {
            items.sort();
            M::Set(items, rest)
        }
        other => other,
    }
}

/// The alpha-equivalence class of `m`, as a term.
fn alpha(m: &M) -> M {
    sorted(&level_rename(m, "%", &mut Vec::new()))
}

/// The reference result: rename the body's binders apart, then substitute textually.
fn reference(body: &M, target: &str, replacement: &M) -> M {
    textual(
        &level_rename(body, "#", &mut Vec::new()),
        target,
        replacement,
    )
}

/// Whether the backend term for `m` is a concrete value of free constructors (its
/// `constructor_like` attribute): no `\and` (a rest is one), no opaque subterm, no repeated
/// key or element.
fn constructor_like(m: &M) -> bool {
    !any_node(m, &|node| match node {
        M::And(..) | M::NumVar(_) | M::NumOf(_) | M::Hole(_) => true,
        M::Map(_, Some(_)) | M::List(_, Some(_), _) | M::Set(_, Some(_)) => true,
        M::Map(entries, None) => has_repeat(entries.iter().map(|(k, _)| k)),
        M::Set(items, None) => has_repeat(items.iter()),
        _ => false,
    })
}

fn has_repeat<'a>(items: impl Iterator<Item = &'a M>) -> bool {
    let items = items.map(sorted).collect::<Vec<_>>();
    let distinct = items.iter().collect::<BTreeSet<_>>();
    distinct.len() != items.len()
}

/// Whether `l` and `r` denote distinct values for every instance of their opaque subterms:
/// they differ in a constructor or a `KVar` token at a position that no opaque subterm,
/// collection rest, map or set covers (constructor terms are equal only when they are the same
/// term). A value of `\and(a, b)` is a value of `a` and of `b`.
fn definitely_distinct(l: &M, r: &M) -> bool {
    match (l, r) {
        (M::And(a, b), other) | (other, M::And(a, b)) => {
            definitely_distinct(a, other) || definitely_distinct(b, other)
        }
        (M::Hole(_), _) | (_, M::Hole(_)) => false,
        (M::Map(..), M::Map(..)) | (M::Set(..), M::Set(..)) => false,
        (M::List(_, Some(_), _), M::List(..)) | (M::List(..), M::List(_, Some(_), _)) => false,
        (M::NumVar(_) | M::NumOf(_), M::NumVar(_) | M::NumOf(_)) => false,
        (M::Var(a), M::Var(b)) => a != b,
        (M::Lam(x, a), M::Lam(y, b)) => x != y || definitely_distinct(a, b),
        (M::Let(x, a, c), M::Let(y, b, d)) => {
            x != y || definitely_distinct(a, b) || definitely_distinct(c, d)
        }
        (M::App(a, c), M::App(b, d)) => definitely_distinct(a, b) || definitely_distinct(c, d),
        (M::List(a, None, _), M::List(b, None, _)) => {
            a.len() != b.len() || a.iter().zip(b).any(|(a, b)| definitely_distinct(a, b))
        }
        // Every other pair has different head constructors (or injections from disjoint sorts).
        _ => true,
    }
}

/// The two sides of an `\and` node or of a collection rest.
fn conjunction(m: &M) -> Option<(&M, &M)> {
    match m {
        M::And(l, r) => Some((l, r)),
        _ => rest_of(m).map(|rest| (&rest.0, &rest.1)),
    }
}

/// Whether the term for `m` denotes no value by a fact the model decides: an `\and` of two
/// definitely distinct sides.
fn denotes_bottom(m: &M) -> bool {
    any_node(m, &|node| {
        conjunction(node).is_some_and(|(l, r)| definitely_distinct(l, r))
    })
}

fn blocking(m: &M) -> bool {
    any_node(m, &|node| matches!(node, M::Hole(_)))
}

/// Why the backend may answer `\bottom` or no value for this call, and what it must rename.
#[derive(Debug, Default)]
struct Reasons {
    /// A map whose keys may collide for some instance once one of them changed (an opaque key,
    /// or a rest), an `\and` of distinct sides that the substitution reaches (the image of an
    /// intersection is not the intersection of the images), or such an `\and` in the
    /// replacement where it is renamed.
    not_applicable: Vec<&'static str>,
    /// Two keys (elements) of one map (set) whose images are alpha-equivalent, or an `\and` of
    /// two distinct concrete values (it denotes no value).
    bottom: Vec<&'static str>,
    /// Binders the target occurs under whose name is not free in the replacement: a binder
    /// of the replacement with that name may be renamed apart.
    conflicts: BTreeSet<String>,
    /// Binders the target occurs under whose name is free in the replacement: capture.
    captures: usize,
}

/// Walks the body (`orig`) and its level-renamed copy (`renamed`, where every remaining
/// `Var(target)` is a free occurrence) in step.
fn reasons(
    orig: &M,
    renamed: &M,
    target: &str,
    replacement: &M,
    replacement_free: &BTreeSet<String>,
    out: &mut Reasons,
) {
    let occurs = |m: &M| mentions(m, target);
    let changes = |m: &M| occurs(m) && *replacement != M::Var(target.to_owned());
    match (orig, renamed) {
        (M::Lam(name, _), M::Lam(_, body)) | (M::Let(name, ..), M::Let(_, _, body))
            if occurs(body) =>
        {
            if replacement_free.contains(name) {
                out.captures += 1;
            } else {
                out.conflicts.insert(name.clone());
            }
        }
        (M::Map(_, rest), M::Map(entries, _)) => {
            let images = entries
                .iter()
                .map(|(k, _)| textual(k, target, replacement))
                .collect::<Vec<_>>();
            if entries.iter().any(|(k, _)| changes(k))
                && (rest.is_some() || !images.iter().all(constructor_like))
            {
                out.not_applicable.push("a changed map key");
            }
            if has_repeat(images.iter().map(alpha).collect::<Vec<_>>().iter()) {
                out.bottom.push("alpha-equivalent map keys");
            }
        }
        (M::Set(..), M::Set(items, _)) => {
            let images = items
                .iter()
                .map(|i| alpha(&textual(i, target, replacement)))
                .collect::<Vec<_>>();
            if has_repeat(images.iter()) {
                out.bottom.push("alpha-equivalent set elements");
            }
        }
        _ => {}
    }
    if let (Some((ol, or)), Some((rl, rr))) = (conjunction(orig), conjunction(renamed))
        && ol != or
        && (occurs(rl) || occurs(rr))
    {
        if constructor_like(ol) && constructor_like(or) {
            out.bottom.push("\\and of distinct concrete values");
        } else {
            out.not_applicable.push("\\and of distinct sides");
        }
    }
    for (o, r) in children(orig).into_iter().zip(children(renamed)) {
        reasons(o, r, target, replacement, replacement_free, out);
    }
}

// ---------------------------------------------------------------------------------------------
// The backend side: building terms and reading results back.

struct Signature {
    lambda: Arc<Symbol>,
    let_: Arc<Symbol>,
    app: Arc<Symbol>,
    num: Arc<Symbol>,
    g: Arc<Symbol>,
    map_e: Arc<Symbol>,
    list_e: Arc<Symbol>,
    set_e: Arc<Symbol>,
    map: Arc<MapDefinition>,
    list: Arc<ListDefinition>,
    set: Arc<ListDefinition>,
    facts: KVarSorts,
    graph: SortGraph,
}

fn kvar_sort() -> Sort {
    Sort::simple("SortKVar")
}
fn exp_sort() -> Sort {
    Sort::simple("SortExp")
}
fn val_sort() -> Sort {
    Sort::simple("SortVal")
}
fn int_sort() -> Sort {
    Sort::simple("SortInt")
}

fn collection_symbols(prefix: &str) -> CollectionSymbols {
    CollectionSymbols {
        unit: format!("{prefix}-unit").into(),
        element: format!("{prefix}-element").into(),
        concat: format!("{prefix}-concat").into(),
    }
}

impl Signature {
    fn new() -> Self {
        let constructor = |name: &str, arguments: Vec<Sort>, result: Sort| {
            Arc::new(Symbol::constructor(name, arguments, result))
        };
        let binder = |name: &str, arguments: Vec<Sort>, result: Sort| {
            let mut symbol = Symbol::constructor(name, arguments, result);
            symbol.attributes.binder = true;
            Arc::new(symbol)
        };
        let mut g = Symbol::constructor("g", vec![exp_sort()], int_sort());
        g.attributes.symbol_type = SymbolType::Function(crate::term::FunctionType::Total);
        let mut graph = SortGraph::default();
        for sort in [
            "SortKVar", "SortVal", "SortInt", "SortMap", "SortList", "SortSet",
        ] {
            graph.insert(sort, [sort.into()]);
        }
        graph.insert(
            "SortExp",
            ["SortExp".into(), "SortKVar".into(), "SortVal".into()],
        );
        Self {
            lambda: binder("lambda", vec![kvar_sort(), exp_sort()], val_sort()),
            let_: binder("let", vec![kvar_sort(), exp_sort(), exp_sort()], exp_sort()),
            app: constructor("app", vec![exp_sort(), exp_sort()], exp_sort()),
            num: constructor("num", vec![int_sort()], exp_sort()),
            g: Arc::new(g),
            map_e: constructor("mapE", vec![Sort::simple("SortMap")], exp_sort()),
            list_e: constructor("listE", vec![Sort::simple("SortList")], exp_sort()),
            set_e: constructor("setE", vec![Sort::simple("SortSet")], exp_sort()),
            map: Arc::new(MapDefinition {
                symbols: collection_symbols("map"),
                key_sort: Sort::simple("SortExp"),
                value_sort: Sort::simple("SortExp"),
                map_sort: "SortMap".into(),
            }),
            list: Arc::new(ListDefinition {
                symbols: collection_symbols("list"),
                element_sort: Sort::simple("SortExp"),
                list_sort: "SortList".into(),
            }),
            set: Arc::new(ListDefinition {
                symbols: collection_symbols("set"),
                element_sort: Sort::simple("SortExp"),
                list_sort: "SortSet".into(),
            }),
            facts: KVarSorts {
                tokens: BTreeMap::from([("SortKVar".into(), Some(DomainKind::Token))]),
                kvar_free: BTreeSet::from(["SortInt".into()]),
            },
            graph,
        }
    }

    fn token(name: &str) -> Term {
        Term::raw_domain_value(kvar_sort(), name)
    }

    fn apply(symbol: &Arc<Symbol>, arguments: Vec<Term>) -> Term {
        Term::application(symbol.clone(), Vec::new(), arguments)
    }

    fn terms(&self, items: &[M]) -> Vec<Term> {
        items.iter().map(|i| self.term(i)).collect()
    }

    /// The collection term (map, list or set sort) that a `Map`, `List` or `Set` node wraps.
    fn collection(&self, m: &M) -> Term {
        let rest = |rest: &Option<Rest>| {
            rest.as_ref()
                .map(|rest| Term::and(self.collection(&rest.0), self.collection(&rest.1)))
        };
        match m {
            M::Map(entries, r) => Term::map(
                self.map.clone(),
                entries
                    .iter()
                    .map(|(k, v)| (self.term(k), self.term(v)))
                    .collect(),
                rest(r),
            ),
            M::List(heads, r, tails) => Term::list(
                self.list.clone(),
                self.terms(heads),
                rest(r).map(|middle| (middle, self.terms(tails))),
            ),
            M::Set(items, r) => Term::set(self.set.clone(), self.terms(items), rest(r)),
            _ => unreachable!("not a collection: {m:?}"),
        }
    }

    /// The backend term for `m`, at the expression sort.
    fn term(&self, m: &M) -> Term {
        match m {
            M::Var(name) => Term::injection(kvar_sort(), exp_sort(), Self::token(name)),
            M::Lam(name, body) => Term::injection(
                val_sort(),
                exp_sort(),
                Self::apply(&self.lambda, vec![Self::token(name), self.term(body)]),
            ),
            M::Let(name, middle, body) => Self::apply(
                &self.let_,
                vec![Self::token(name), self.term(middle), self.term(body)],
            ),
            M::App(l, r) => Self::apply(&self.app, vec![self.term(l), self.term(r)]),
            M::And(l, r) => Term::and(self.term(l), self.term(r)),
            M::Map(..) => Self::apply(&self.map_e, vec![self.collection(m)]),
            M::List(..) => Self::apply(&self.list_e, vec![self.collection(m)]),
            M::Set(..) => Self::apply(&self.set_e, vec![self.collection(m)]),
            M::NumVar(name) => Self::apply(
                &self.num,
                vec![Term::variable(Variable::new(name.as_str(), int_sort()))],
            ),
            M::NumOf(inner) => Self::apply(
                &self.num,
                vec![Self::apply(&self.g, vec![self.term(inner)])],
            ),
            M::Hole(name) => Term::variable(Variable::new(name.as_str(), exp_sort())),
        }
    }

    fn models<'t>(&self, items: impl IntoIterator<Item = &'t Term>) -> Result<Vec<M>, String> {
        items.into_iter().map(|i| self.model(i)).collect()
    }

    /// Reads a collection term back: the sort `wrapper` takes, with an optional `\and` rest
    /// (an empty collection with a rest is the rest itself).
    fn model_collection(&self, wrapper: &Arc<Symbol>, term: &Term) -> Result<M, String> {
        if term.sort() != wrapper.argument_sorts[0] {
            return Err(format!("a collection of the wrong sort: {term:?}"));
        }
        let rest = |rest: &Term| -> Result<Rest, String> {
            let TermKind::And(l, r) = rest.kind() else {
                return Err(format!("a rest that is not a conjunction: {rest:?}"));
            };
            let side = |side: &Term| match self.model_collection(wrapper, side)? {
                side if rest_of(&side).is_none() => Ok(side),
                side => Err(format!("a rest side with a rest: {side:?}")),
            };
            Ok(Box::new((side(l)?, side(r)?)))
        };
        Ok(match term.kind() {
            TermKind::Map {
                entries, rest: r, ..
            } => M::Map(
                entries
                    .iter()
                    .map(|(k, v)| Ok((self.model(k)?, self.model(v)?)))
                    .collect::<Result<_, String>>()?,
                r.as_ref().map(rest).transpose()?,
            ),
            TermKind::List { heads, rest: r, .. } => {
                let (r, tails) = match r {
                    Some((middle, tails)) => (Some(rest(middle)?), self.models(tails)?),
                    None => (None, Vec::new()),
                };
                M::List(self.models(heads)?, r, tails)
            }
            TermKind::Set {
                elements, rest: r, ..
            } => M::Set(self.models(elements)?, r.as_ref().map(rest).transpose()?),
            TermKind::And(..) => {
                let r = Some(rest(term)?);
                if wrapper == &self.map_e {
                    M::Map(Vec::new(), r)
                } else if wrapper == &self.list_e {
                    M::List(Vec::new(), r, Vec::new())
                } else {
                    M::Set(Vec::new(), r)
                }
            }
            _ => return Err(format!("not a collection: {term:?}")),
        })
    }

    /// Reads a backend term of the expression sort back into the model, rejecting any term
    /// this signature cannot build (a sort error included).
    fn model(&self, term: &Term) -> Result<M, String> {
        if term.sort() != exp_sort() {
            return Err(format!("a subterm is not at the expression sort: {term:?}"));
        }
        let unexpected = || Err(format!("unexpected subterm {term:?}"));
        Ok(match term.kind() {
            TermKind::Injection { term: inner, .. } => match inner.kind() {
                TermKind::DomainValue { .. } => M::Var(self.declaration(inner)?),
                TermKind::Application {
                    symbol, arguments, ..
                } if symbol == &self.lambda => M::Lam(
                    self.declaration(&arguments[0])?,
                    b(self.model(&arguments[1])?),
                ),
                _ => return unexpected(),
            },
            TermKind::Application {
                symbol, arguments, ..
            } => {
                let argument = |index: usize| self.model(&arguments[index]).map(b);
                if symbol == &self.let_ {
                    M::Let(self.declaration(&arguments[0])?, argument(1)?, argument(2)?)
                } else if symbol == &self.app {
                    M::App(argument(0)?, argument(1)?)
                } else if symbol == &self.num {
                    match arguments[0].kind() {
                        TermKind::Variable(variable) => M::NumVar(variable.name.to_string()),
                        TermKind::Application {
                            symbol, arguments, ..
                        } if symbol == &self.g => M::NumOf(b(self.model(&arguments[0])?)),
                        _ => return unexpected(),
                    }
                } else if [&self.map_e, &self.list_e, &self.set_e].contains(&symbol) {
                    self.model_collection(symbol, &arguments[0])?
                } else {
                    return unexpected();
                }
            }
            TermKind::And(l, r) => M::And(b(self.model(l)?), b(self.model(r)?)),
            TermKind::Variable(variable) => M::Hole(variable.name.to_string()),
            _ => return unexpected(),
        })
    }

    fn declaration(&self, term: &Term) -> Result<String, String> {
        read_kvar(term, &self.facts.tokens)
            .filter(|_| term.sort() == kvar_sort())
            .map(|name| name.to_string())
            .ok_or_else(|| format!("not a KVar token: {term:?}"))
    }

    fn subst(&self, body: &M, replacement: &M, target: &str) -> BuiltinResult {
        subst_one(
            &[self.term(body), self.term(replacement), Self::token(target)],
            &self.facts,
            &self.graph,
        )
        .expect("no step deadline is active")
    }
}

/// Whether some map (set) in the model of a result binds a key (holds an element) twice: a
/// term that denotes no value, which the backend must report as `\bottom`, not return.
fn syntactic_repeat(m: &M) -> bool {
    any_node(m, &|node| match node {
        M::Map(entries, _) => {
            entries
                .iter()
                .map(|(k, _)| k)
                .collect::<BTreeSet<_>>()
                .len()
                != entries.len()
        }
        M::Set(items, _) => items.iter().collect::<BTreeSet<_>>().len() != items.len(),
        _ => false,
    })
}

// ---------------------------------------------------------------------------------------------
// Generators.

fn name() -> impl Strategy<Value = String> + Clone {
    prop::sample::select(&NAMES[..]).prop_map(str::to_owned)
}

fn dedup_keys(entries: Vec<(M, M)>) -> Vec<(M, M)> {
    let mut seen = BTreeSet::new();
    entries
        .into_iter()
        .filter(|(k, _)| seen.insert(k.clone()))
        .collect()
}

fn dedup(items: Vec<M>) -> Vec<M> {
    let mut seen = BTreeSet::new();
    items
        .into_iter()
        .filter(|i| seen.insert(i.clone()))
        .collect()
}

/// Concrete constructor terms (map keys).
fn ground() -> BoxedStrategy<M> {
    name()
        .prop_map(M::Var)
        .prop_recursive(3, 10, 2, |inner| {
            prop_oneof![
                3 => (name(), inner.clone()).prop_map(|(n, body)| M::Lam(n, b(body))),
                1 => (name(), inner.clone(), inner.clone())
                    .prop_map(|(n, m, body)| M::Let(n, b(m), b(body))),
                2 => (inner.clone(), inner.clone()).prop_map(|(l, r)| M::App(b(l), b(r))),
                1 => vec(inner, 0..3).prop_map(|items| M::List(items, None, Vec::new())),
            ]
        })
        .boxed()
}

/// Map keys: often a bare token, so that a substitution can make two keys one.
fn key() -> BoxedStrategy<M> {
    prop_oneof![3 => name().prop_map(M::Var), 1 => ground()].boxed()
}

/// A rest one time in four: `\and(L, R)` of two collections `make` builds, with `R = L` half
/// of the time.
fn rest(make: BoxedStrategy<M>) -> impl Strategy<Value = Option<Rest>> {
    prop_oneof![
        3 => Just(None),
        1 => (make.clone(), make, any::<bool>()).prop_map(|(l, r, same)| {
            let r = if same { l.clone() } else { r };
            Some(Box::new((l, r)))
        }),
    ]
}

fn expression() -> BoxedStrategy<M> {
    prop_oneof![
        30 => name().prop_map(M::Var),
        2 => Just(M::NumVar("N".to_owned())),
        1 => Just(M::Hole("H".to_owned())),
    ]
    .prop_recursive(4, 24, 3, |inner| {
        let entries = vec((key(), inner.clone()), 0..4).prop_map(dedup_keys);
        let items = vec(inner.clone(), 0..4);
        let elements = items.clone().prop_map(dedup);
        let map = entries.clone().prop_map(|e| M::Map(e, None)).boxed();
        let list = items
            .clone()
            .prop_map(|i| M::List(i, None, Vec::new()))
            .boxed();
        let set = elements.clone().prop_map(|i| M::Set(i, None)).boxed();
        prop_oneof![
            6 => (name(), inner.clone()).prop_map(|(n, body)| M::Lam(n, b(body))),
            2 => (name(), inner.clone(), inner.clone())
                .prop_map(|(n, m, body)| M::Let(n, b(m), b(body))),
            3 => (inner.clone(), inner.clone()).prop_map(|(l, r)| M::App(b(l), b(r))),
            // `\and` of one term, of two terms, or of two terms one token apart (which a
            // substitution of one token by the other identifies).
            3 => (inner.clone(), inner.clone(), 0..4u8, name(), name()).prop_map(
                |(l, r, shape, from, to)| {
                    let r = match shape {
                        0 | 1 => l.clone(),
                        2 => r,
                        _ => textual(&l, &from, &M::Var(to)),
                    };
                    M::And(b(l), b(r))
                }
            ),
            2 => (entries, rest(map)).prop_map(|(e, r)| M::Map(e, r)),
            2 => (items.clone(), rest(list), items).prop_map(|(heads, r, tails)| {
                let tails = if r.is_some() { tails } else { Vec::new() };
                M::List(heads, r, tails)
            }),
            2 => (elements, rest(set)).prop_map(|(i, r)| M::Set(i, r)),
            1 => inner.prop_map(|i| M::NumOf(b(i))),
        ]
    })
    .boxed()
}

#[derive(Clone, Debug)]
struct Case {
    body: M,
    replacement: M,
    target: String,
}

/// The target is a free name of the body three times in four, so that most calls substitute.
fn case() -> impl Strategy<Value = Case> {
    (
        expression(),
        prop_oneof![
            3 => expression(),
            1 => name().prop_map(M::Var),
        ],
    )
        .prop_flat_map(|(body, replacement)| {
            let free = fv(&body).into_iter().collect::<Vec<_>>();
            let target = if free.is_empty() {
                name().boxed()
            } else {
                prop_oneof![3 => prop::sample::select(free), 1 => name()].boxed()
            };
            (Just(body), Just(replacement), target)
        })
        .prop_map(|(body, replacement, target)| Case {
            body,
            replacement,
            target,
        })
}

fn runner() -> TestRunner {
    TestRunner::new_with_rng(
        Config {
            cases: CASES,
            failure_persistence: None,
            ..Config::default()
        },
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    )
}

// ---------------------------------------------------------------------------------------------
// The properties.

#[derive(Debug, Default)]
struct Tally {
    values: u32,
    bottoms: u32,
    not_applicable: u32,
    blocked: u32,
    captures: u32,
    renamed_replacement_binders: u32,
    and_reached: u32,
    collections_reached: u32,
    rests_reached: u32,
    map_key_collisions: u32,
}

fn check_case(signature: &Signature, case: &Case, tally: &mut Tally) -> Result<(), String> {
    let Case {
        body,
        replacement,
        target,
    } = case;
    let replacement_free = fv(replacement);
    let renamed = level_rename(body, "#", &mut Vec::new());
    let mut why = Reasons::default();
    reasons(
        body,
        &renamed,
        target,
        replacement,
        &replacement_free,
        &mut why,
    );
    let mut replacement_binders = BTreeSet::new();
    binder_names(replacement, &mut replacement_binders);
    let freshened = why.conflicts.intersection(&replacement_binders).count() > 0;
    if freshened
        && any_node(replacement, &|node| {
            conjunction(node).is_some_and(|(l, r)| l != r)
        })
    {
        why.not_applicable
            .push("an \\and of distinct sides in a replacement renamed apart");
    }
    let blocked = blocking(body) || blocking(replacement);
    let occurs = mentions(&renamed, target);

    let result = signature.subst(body, replacement, target);
    match &result {
        BuiltinResult::NotApplicable if blocked => tally.blocked += 1,
        BuiltinResult::NotApplicable => {
            if why.not_applicable.is_empty() {
                return Err(format!("no value without a reason ({why:?})"));
            }
            tally.not_applicable += 1;
        }
        BuiltinResult::Bottom => {
            if blocked || why.bottom.is_empty() {
                return Err(format!("\\bottom without a reason ({why:?})"));
            }
            tally.bottoms += 1;
            if why.bottom.contains(&"alpha-equivalent map keys") {
                tally.map_key_collisions += 1;
            }
        }
        BuiltinResult::Value(term) => {
            if blocked {
                return Err("a value despite an opaque subterm that may hold a KVar".into());
            }
            let actual = signature.model(term)?;
            let expected = reference(body, target, replacement);
            if alpha(&actual) != alpha(&expected) {
                return Err(format!(
                    "not alpha-equivalent to the renamed textual substitution\n  actual   \
                     {actual:?}\n  expected {expected:?}"
                ));
            }
            let mut free = fv(body);
            free.remove(target);
            if occurs {
                free.extend(replacement_free.iter().cloned());
            }
            if fv(&actual) != free {
                return Err(format!("free KVars {:?}, expected {free:?}", fv(&actual)));
            }
            // `substOne` applied to no value is no value, and a value is mapped to a value.
            let argument_bottom = denotes_bottom(body) || (occurs && denotes_bottom(replacement));
            if denotes_bottom(&actual) != argument_bottom {
                return Err(if argument_bottom {
                    format!("the argument denotes no value, the result {actual:?} denotes one")
                } else {
                    format!("the argument denotes a value, the result {actual:?} denotes none")
                });
            }
            if syntactic_repeat(&actual) {
                return Err(format!("a value binding a key twice: {actual:?}"));
            }
            tally.values += 1;
            if why.captures > 0 {
                tally.captures += 1;
            }
            if freshened {
                tally.renamed_replacement_binders += 1;
            }
            let reached = |test: &dyn Fn(&M) -> bool| occurs && any_node(body, test);
            if reached(&|node| matches!(node, M::And(..))) {
                tally.and_reached += 1;
            }
            if reached(&|node| matches!(node, M::Map(..) | M::Set(..))) {
                tally.collections_reached += 1;
            }
            if reached(&|node| rest_of(node).is_some()) {
                tally.rests_reached += 1;
            }
        }
        _ => return Err(format!("{result:?}")),
    }
    if !blocked && why.not_applicable.is_empty() && why.bottom.is_empty() {
        let BuiltinResult::Value(_) = result else {
            return Err(format!("{result:?} without a reason"));
        };
    }
    Ok(())
}

fn run_property(
    name: &str,
    check: impl Fn(&Signature, &Case, &mut Tally) -> Result<(), String>,
) -> Tally {
    let signature = Signature::new();
    let tally = RefCell::new(Tally::default());
    let outcome = runner().run(&case(), |case| {
        check(&signature, &case, &mut tally.borrow_mut()).map_err(TestCaseError::fail)
    });
    if let Err(error) = outcome {
        panic!("{name}: {error}");
    }
    tally.into_inner()
}

/// The result is alpha-equivalent to textual substitution into the body with its binders
/// renamed apart, has the expected free `KVar`s, keeps whether the argument denotes a value,
/// and every `\bottom` or unevaluated call has a reason in the semantics of maps, sets and
/// `\and`.
#[test]
fn substitution_is_capture_avoiding_and_alpha_equivalent_to_the_renamed_reference() {
    let tally = run_property("capture-avoiding", check_case);
    eprintln!("{tally:?}");
    // Guards against a vacuous pass: the generator must reach each kind of decision.
    assert!(tally.values * 2 > CASES, "{tally:?}");
    assert!(tally.captures * 20 > tally.values, "{tally:?}");
    assert!(
        tally.renamed_replacement_binders * 40 > tally.values,
        "{tally:?}"
    );
    assert!(tally.and_reached * 20 > tally.values, "{tally:?}");
    assert!(tally.collections_reached * 10 > tally.values, "{tally:?}");
    assert!(tally.rests_reached * 40 > tally.values, "{tally:?}");
    assert!(
        tally.map_key_collisions > 0
            && tally.bottoms > 0
            && tally.not_applicable > 0
            && tally.blocked > 0,
        "{tally:?}"
    );
}

/// Strips `\and(T, T)` to `T`, everywhere.
fn collapse(m: &M) -> M {
    match m {
        M::And(l, r) if l == r => collapse(l),
        _ => map_children(m, &mut collapse),
    }
}

fn kind(result: &BuiltinResult) -> &'static str {
    match result {
        BuiltinResult::Value(_) => "value",
        BuiltinResult::Bottom => "bottom",
        BuiltinResult::NotApplicable => "not applicable",
        _ => "unsupported",
    }
}

/// `\and(T, T)` denotes the value `T` denotes, and `substOne` is a function of the values of its
/// arguments: substituting into `\and(B, B)`, or with the replacement `\and(R, R)`, gives the
/// result for `B` and `R` (as `\and(V, V)` where the copy stands). Renaming the two copies
/// apart differently would give `\and(V, V')` with `V != V'`, which denotes no value.
#[test]
fn and_idempotence() {
    let doubled_values = RefCell::new((0u32, 0u32));
    run_property("and-idempotence", |signature, case, _| {
        let Case {
            body,
            replacement,
            target,
        } = case;
        let plain = signature.subst(body, replacement, target);
        let doubled_body = M::And(b(body.clone()), b(body.clone()));
        match (&plain, signature.subst(&doubled_body, replacement, target)) {
            (BuiltinResult::Value(plain), BuiltinResult::Value(doubled)) => {
                if doubled != Term::and(plain.clone(), plain.clone()) {
                    return Err(format!(
                        "\\and(B, B) gave {:?}, B gave {:?}",
                        signature.model(&doubled)?,
                        signature.model(plain)?
                    ));
                }
                doubled_values.borrow_mut().0 += 1;
            }
            (plain, doubled) if kind(plain) == kind(&doubled) => {}
            (plain, doubled) => {
                return Err(format!(
                    "\\and(B, B) gave {}, B gave {}",
                    kind(&doubled),
                    kind(plain)
                ));
            }
        }
        let doubled_replacement = M::And(b(replacement.clone()), b(replacement.clone()));
        let doubled = signature.subst(body, &doubled_replacement, target);
        match (&plain, &doubled) {
            (BuiltinResult::Value(plain), BuiltinResult::Value(doubled)) => {
                let (plain, doubled) = (signature.model(plain)?, signature.model(doubled)?);
                if sorted(&collapse(&plain)) != sorted(&collapse(&doubled)) {
                    return Err(format!(
                        "replacement \\and(R, R) gave {doubled:?}, R gave {plain:?}"
                    ));
                }
                doubled_values.borrow_mut().1 += 1;
            }
            // `\and(R, R)` is not a concrete value, so a map key it enters can no longer be
            // shown distinct from (or equal to) the other keys: no value is a sound answer.
            (_, BuiltinResult::NotApplicable)
                if any_node(body, &|node| matches!(node, M::Map(..))) => {}
            // Two copies of `R` in one set (map keys) make it `\bottom`; with `\and(R, R)` the
            // copies are no longer the same term, and the value returned is a collection that
            // repeats an element once `\and(R, R)` is read as `R`: it denotes no value either.
            (BuiltinResult::Bottom, BuiltinResult::Value(doubled))
                if syntactic_repeat(&sorted(&collapse(&signature.model(doubled)?))) => {}
            (plain, doubled) if kind(plain) == kind(doubled) => {}
            (plain, doubled) => {
                return Err(format!(
                    "replacement \\and(R, R) gave {}, R gave {}",
                    kind(doubled),
                    kind(plain)
                ));
            }
        }
        Ok(())
    });
    let (body_values, replacement_values) = doubled_values.into_inner();
    assert!(
        body_values * 2 > CASES && replacement_values * 2 > CASES,
        "{body_values} {replacement_values}"
    );
}

fn var(name: &str) -> M {
    M::Var(name.to_owned())
}

fn lam(name: &str, body: M) -> M {
    M::Lam(name.to_owned(), b(body))
}

#[test]
fn opaque_integer_arguments_are_neither_substituted_nor_renamed() {
    // `g(y)` is an integer computed from the token `y`; renaming the binder `y` must leave it.
    let signature = Signature::new();
    let opaque = || b(M::NumOf(b(M::App(b(var("x")), b(var("y"))))));
    let body = lam("y", M::App(b(var("x")), opaque()));
    let BuiltinResult::Value(result) = signature.subst(&body, &var("y"), "x") else {
        panic!("expected a value");
    };
    assert_eq!(
        signature.model(&result).unwrap(),
        lam("y0", M::App(b(var("y")), opaque()))
    );
}

/// `t` at each position of each collection kind: map key, value and rest; list head, middle and
/// tail; set element and rest; and both sides of an `\and`. Rests have equal sides, so that no
/// position stops the substitution, and sit beside an entry `w`, without which the collection
/// would be its rest.
fn every_position(t: &M) -> Vec<M> {
    let (w, z) = (|| var("w"), || var("z"));
    let map = |entries: Vec<(M, M)>| M::Map(entries, None);
    let list = |items: Vec<M>| M::List(items, None, Vec::new());
    let set = |items: Vec<M>| M::Set(items, None);
    let both = |side: M| Some(Box::new((side.clone(), side)));
    vec![
        map(vec![(t.clone(), z())]),
        map(vec![(z(), t.clone())]),
        M::Map(vec![(w(), w())], both(map(vec![(z(), t.clone())]))),
        list(vec![t.clone()]),
        M::List(vec![w()], both(list(vec![t.clone()])), Vec::new()),
        M::List(Vec::new(), both(list(vec![z()])), vec![t.clone()]),
        set(vec![t.clone()]),
        M::Set(vec![w()], both(set(vec![t.clone()]))),
        M::And(b(t.clone()), b(t.clone())),
    ]
}

/// The generator reaches rests rarely; this walks every collection position once, in the three
/// roles a position plays: the target occurs there under a binder that captures the
/// replacement, plainly, and inside a replacement whose binder is renamed apart (its bound
/// occurrence must follow the renamed binder into the position).
#[test]
fn substitution_and_renaming_reach_every_collection_position() {
    let signature = Signature::new();
    let mut tally = Tally::default();
    let mut cases = Vec::new();
    for position in every_position(&var("x")) {
        cases.push((lam("y", position.clone()), var("y")));
        cases.push((position, var("z")));
    }
    for position in every_position(&var("y")) {
        cases.push((lam("y", var("x")), lam("y", position)));
    }
    for (body, replacement) in &cases {
        let case = Case {
            body: body.clone(),
            replacement: replacement.clone(),
            target: "x".to_owned(),
        };
        check_case(&signature, &case, &mut tally)
            .unwrap_or_else(|error| panic!("{case:?}: {error}"));
    }
    assert_eq!(tally.values as usize, cases.len(), "{tally:?}");
    // A changed key beside a rest may equal a key of the rest for some instance: no value.
    let rest = Some(Box::new((
        M::Map(vec![(var("w"), var("w"))], None),
        M::Map(vec![(var("w"), var("w"))], None),
    )));
    let case = Case {
        body: M::Map(vec![(var("x"), var("z"))], rest),
        replacement: var("z"),
        target: "x".to_owned(),
    };
    check_case(&signature, &case, &mut tally).unwrap();
    assert_eq!(tally.not_applicable, 1, "{tally:?}");
}
