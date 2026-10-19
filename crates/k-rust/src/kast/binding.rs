//! The binding structure of K terms, with variables named by strings.
//!
//! This module states once which occurrences of a name a quantifier binds, and gives the
//! operations that a pass reading or rewriting variables under quantifiers needs: binder
//! recognition ([`quantifier`], [`quantifier_kind`]), the role of every variable occurrence
//! ([`occurrences`]), the free and the bound names ([`free_variables`], [`bound_names`]), the
//! renaming of bound variables ([`rename_bound`]), the renaming apart of a sentence's bound
//! variables ([`rename_apart_in_sentence`]), and capture-avoiding substitution ([`substitute`]).
//!
//! # The rule
//!
//! - A quantifier is an application of `#Exists` or `#Forall` to exactly two arguments,
//!   annotations aside: its binder, then its body.
//!   Nothing else binds here: an application of an `mlBinder` production is an ordinary
//!   application, and so are the patterns of `#fun`, `#let` and match, which bind in the local
//!   functions `resolve_fun` lowers them to.
//! - A quantifier binds the variables of its binder, in its body and nowhere else.
//!   The binder is the bound variable, under annotations, or under a semantic cast before
//!   semantic casts are resolved.
//!   An occurrence of a name is bound by the innermost quantifier around it that binds that name;
//!   an occurrence that no quantifier binds is free.
//!   The variables of a binder are binding occurrences, so they are neither free nor bound.
//! - A binder that is not a variable in that sense (`#Exists f(X, X) . X`) is malformed, since a
//!   quantifier binds a variable, and the definition check is to refuse it with a location.
//!   Until it does, such a quantifier binds each distinct name of a variable in its binder once.
//! - A variable is its name. Within a sentence one name has one sort, so the sort written on an
//!   occurrence never decides which variable it is.
//! - An unresolved anonymous variable (`_`, `?_`, `!_` or `@_`, [`is_unresolved_anonymous`]) is a
//!   variable of its own at each occurrence: a quantifier over one binds nothing, and each of its
//!   other occurrences is free.
//!   Once `resolve anonymous variables` has given each such occurrence its own name, the rule has
//!   no exception: whether a name came from an anonymous variable never decides what binds it.
//!
//! Two terms are alpha-equivalent when they differ only in the names of bound variables, with
//! every occurrence bound by the same quantifier in both; they have the same meaning.
//! [`rename_bound`] with names that capture nothing and [`rename_apart_in_sentence`] give terms
//! alpha-equivalent to their input, and [`substitute`] a term alpha-equivalent to the
//! substitution that respects binding. Each keeps every node's annotations.
//!
//! # Fresh names
//!
//! A bound variable that [`rename_apart_in_sentence`] or [`substitute`] renames takes a name
//! that its [`Reservation`] does not hold: `{name}{n}` for the least `n` the reservation has not
//! tried for that stem, so it keeps its sigil (`?`, `!` or `@`) and its `_` prefix, which mean
//! something of their own. Where `{name}{n}` would read as a name `resolve anonymous variables`
//! gives (`_Gen`, `?_Gen`, `!_Gen` or `@_Gen` followed by digits, or `_DotVar` followed by
//! digits), the stem is `{name}_` instead, so a mint never takes a spelling that passes still
//! read as anonymous.
//!
//! Both operations reserve every name of the terms they are given, so a new name captures
//! nothing there and is captured by nothing. What they are not given, the caller reserves:
//! - the variable names a sentence's attributes mention (`concrete`, `symbolic`,
//!   `unboundVariables`);
//! - the names of the rest of the destination sentence, for a pass that substitutes into one
//!   term of a sentence or moves terms between sentences.
//!
//! This reservation is separate from kompile's own fresh-name generator; a pass that uses both
//! keeps them in step by reserving in each the names the other mints.
#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::{BTreeMap, BTreeSet};

use super::{InternalLabel, Label, Sort, Term};

/// Which quantifier a [`Quantifier`] is.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum QuantifierKind {
    /// `#Exists`.
    Exists,
    /// `#Forall`.
    Forall,
}

/// A quantifier node taken apart; see [`quantifier`].
#[derive(Clone, Copy, Debug)]
pub struct Quantifier<'t> {
    /// Which quantifier it is.
    pub kind: QuantifierKind,
    /// The label, with its sort parameters.
    pub label: &'t Label,
    /// The first argument, as stored: the bound variable.
    pub binder: &'t Term,
    /// The second argument, as stored: the scope of the binder.
    pub body: &'t Term,
}

impl<'t> Quantifier<'t> {
    /// The bound variable's name and sort, when the binder is a variable under any annotations;
    /// `None` while a semantic cast is still around it, or for a binder that is no variable.
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "every other node is no variable"
    )]
    pub fn variable(&self) -> Option<(&'t str, Option<&'t Sort>)> {
        match self.binder.unannotated() {
            Term::Variable { name, sort } => Some((name, sort.as_ref())),
            _ => None,
        }
    }

    /// The names this quantifier binds in its body: the distinct names of the variables of its
    /// binder, in preorder, without the unresolved anonymous ones. A well-formed binder gives at
    /// most one.
    pub fn bound(&self) -> Vec<&'t str> {
        let mut names: Vec<&'t str> = Vec::new();
        let mut pending = vec![self.binder];
        // Invariant: `names` holds the distinct bound names of the binder's nodes visited so far,
        // in preorder, and `pending` the unvisited ones, the next on top; each pop visits one
        // node.
        while let Some(node) = pending.pop() {
            if let Term::Variable { name, .. } = node.unannotated() {
                if !is_unresolved_anonymous(name) && !names.contains(&name.as_str()) {
                    names.push(name.as_str());
                }
            } else {
                pending.extend(node.children().into_iter().rev());
            }
        }
        names
    }
}

/// The quantifier `term` is, annotations aside: an application of `#Exists` or `#Forall` to two
/// arguments; `None` for any other term, including those labels applied to another number of
/// arguments.
pub fn quantifier(term: &Term) -> Option<Quantifier<'_>> {
    let Term::Apply { label, arguments } = term.unannotated() else {
        return None;
    };
    let kind = quantifier_kind(label)?;
    let [binder, body] = arguments.as_slice() else {
        return None;
    };
    Some(Quantifier {
        kind,
        label,
        binder,
        body,
    })
}

/// The quantifier `label` names, whatever its sort parameters: the test [`quantifier`] applies to
/// a term's label, for a reader whose terms are not [`Term`]s yet (a parse tree's productions).
pub fn quantifier_kind(label: &Label) -> Option<QuantifierKind> {
    if label.is(InternalLabel::Exists) {
        Some(QuantifierKind::Exists)
    } else if label.is(InternalLabel::Forall) {
        Some(QuantifierKind::Forall)
    } else {
        None
    }
}

/// Whether `name` is an anonymous variable as written, before `resolve anonymous variables`
/// names it: `_`, `?_`, `!_` or `@_`.
pub fn is_unresolved_anonymous(name: &str) -> bool {
    matches!(name, "_" | "?_" | "!_" | "@_")
}

/// What one variable occurrence is, by the rule of this module.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Role {
    /// No quantifier binds it.
    Free,
    /// The quantifier numbered `binder` binds it: quantifiers are numbered 0, 1, … in the
    /// preorder of the term walked.
    Bound {
        /// The binding quantifier's number.
        binder: usize,
    },
    /// It is a variable of the binder of the quantifier numbered `binder`. An unresolved
    /// anonymous variable there binds nothing, but is still the binder's own.
    Binding {
        /// The quantifier's number.
        binder: usize,
    },
}

/// One variable occurrence of a term; see [`occurrences`].
#[derive(Clone, Copy, Debug)]
pub struct Occurrence<'t> {
    /// The variable node as stored, its annotations (and so its location) included.
    pub node: &'t Term,
    /// The variable's name.
    pub name: &'t str,
    /// The sort written on this occurrence.
    pub sort: Option<&'t Sort>,
    /// Free, bound, or binding.
    pub role: Role,
}

/// Every variable occurrence of `term`, in preorder (a quantifier's binder before its body),
/// with its role.
///
/// The names of the free occurrences are [`free_variables`]; the first-occurrence order of the
/// free names, and the quantifier that binds each bound occurrence, are what a reader numbering
/// variables up to renaming needs. The walk keeps its pending subterms in a work list, so a term
/// of any depth takes no native stack per level.
pub fn occurrences(term: &Term) -> Vec<Occurrence<'_>> {
    let mut found = Vec::new();
    let mut bound: Vec<(&str, usize)> = Vec::new();
    let mut quantifiers = 0_usize;
    // Each item is a term and the number of entries of `bound` in its scope.
    let mut pending: Vec<(&Term, usize)> = vec![(term, 0)];
    // Invariant: `found` holds the occurrences of the nodes visited so far, in preorder;
    // `bound[..scope]` is the names bound around each pending term with their quantifiers'
    // numbers, innermost last; `quantifiers` is the number of quantifiers visited so far.
    while let Some((node, scope)) = pending.pop() {
        bound.truncate(scope);
        if let Some(quantifier) = quantifier(node) {
            let number = quantifiers;
            quantifiers += 1;
            let mut binder = vec![quantifier.binder];
            // Invariant: the variables of the binder's nodes visited so far are in `found`, in
            // preorder; `binder` holds the unvisited ones, the next on top.
            while let Some(part) = binder.pop() {
                if let Term::Variable { name, sort } = part.unannotated() {
                    found.push(Occurrence {
                        node: part,
                        name,
                        sort: sort.as_ref(),
                        role: Role::Binding { binder: number },
                    });
                } else {
                    binder.extend(part.children().into_iter().rev());
                }
            }
            bound.extend(quantifier.bound().into_iter().map(|name| (name, number)));
            pending.push((quantifier.body, bound.len()));
            continue;
        }
        match node.unannotated() {
            Term::Variable { name, sort } => {
                let role = bound
                    .iter()
                    .rev()
                    .find(|(bound, _)| *bound == name)
                    .map_or(Role::Free, |(_, binder)| Role::Bound { binder: *binder });
                found.push(Occurrence {
                    node,
                    name,
                    sort: sort.as_ref(),
                    role,
                });
            }
            other @ (Term::InjectedLabel(_)
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::Apply { .. }
            | Term::Token { .. }
            | Term::Annotated { .. }) => {
                pending.extend(
                    other
                        .children()
                        .into_iter()
                        .rev()
                        .map(|child| (child, scope)),
                );
            }
        }
    }
    found
}

/// The names that occur free in `term`; `_` (or `?_`, `!_`, `@_`) is among them when an
/// unresolved anonymous variable of that spelling occurs outside a binder.
///
/// The walk keeps its pending subterms in a work list, so a term of any depth takes no native
/// stack per level.
pub fn free_variables(term: &Term) -> BTreeSet<String> {
    let mut free = BTreeSet::new();
    let mut bound: Vec<&str> = Vec::new();
    // Each item is a term and the number of entries of `bound` in its scope.
    let mut pending: Vec<(&Term, usize)> = vec![(term, 0)];
    // Invariant: every term popped from `pending` is a subterm of `term`, visited once, so the
    // loop ends; `bound[..scope]` is the names bound around each pending term, innermost last.
    while let Some((node, scope)) = pending.pop() {
        bound.truncate(scope);
        if let Some(quantifier) = quantifier(node) {
            bound.extend(quantifier.bound());
            pending.push((quantifier.body, bound.len()));
            continue;
        }
        match node.unannotated() {
            Term::Variable { name, .. } => {
                if !bound.contains(&name.as_str()) {
                    free.insert(name.clone());
                }
            }
            other @ (Term::InjectedLabel(_)
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Sequence(_)
            | Term::Apply { .. }
            | Term::Token { .. }
            | Term::Annotated { .. }) => {
                for child in other.children() {
                    pending.push((child, scope));
                }
            }
        }
    }
    free
}

/// The names the quantifiers of `term` bind, in preorder: each quantifier's
/// [`Quantifier::bound`] in turn, so a name bound by two quantifiers occurs twice.
pub fn bound_names(term: &Term) -> Vec<String> {
    let mut names = Vec::new();
    let mut pending = vec![term];
    // Invariant: `names` holds the bound names of the quantifiers visited so far, in preorder,
    // and `pending` the unvisited subterms that can hold a quantifier, the next on top.
    while let Some(node) = pending.pop() {
        if let Some(quantifier) = quantifier(node) {
            names.extend(quantifier.bound().into_iter().map(str::to_owned));
            pending.push(quantifier.body);
        } else {
            pending.extend(node.children().into_iter().rev());
        }
    }
    names
}

/// Rename bound variables in `term`: each quantifier, in preorder, asks `rename` once for each
/// name it binds ([`Quantifier::bound`]); where `rename` gives a new name, every variable of that
/// name in the binder and every occurrence the quantifier binds take it.
///
/// Free occurrences, and occurrences a nested quantifier binds again, keep their names.
/// The result is alpha-equivalent to `term` when no new name is free in the body of its
/// quantifier or bound by a quantifier inside it around an occurrence it renames; a new name
/// that occurs nowhere in `term` meets both.
pub fn rename_bound(term: &mut Term, rename: &mut impl FnMut(&str) -> Option<String>) {
    rename_in(term, &mut Vec::new(), rename);
}

/// Names that fresh names must avoid, with the next suffix to try for each stem (module
/// documentation, "Fresh names").
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Reservation {
    names: BTreeSet<String>,
    next: BTreeMap<String, usize>,
}

impl Reservation {
    /// A reservation holding no name.
    pub fn new() -> Self {
        Self::default()
    }

    /// Reserve `name`.
    pub fn reserve(&mut self, name: impl Into<String>) {
        self.names.insert(name.into());
    }

    /// Whether `name` is reserved.
    pub fn contains(&self, name: &str) -> bool {
        self.names.contains(name)
    }

    /// The reserved names.
    pub fn names(&self) -> &BTreeSet<String> {
        &self.names
    }

    /// Reserve the name of every variable of `term`, binders included.
    pub fn reserve_names_of(&mut self, term: &Term) {
        term.visit_preorder(&mut |node| {
            if let Term::Variable { name, .. } = node {
                self.names.insert(name.clone());
            }
        });
    }

    /// A new name for a variable named `name`, reserved: `{name}{n}` for the least `n` not yet
    /// tried for that stem whose name is not reserved (module documentation, "Fresh names").
    /// Successive mints of one stem over names it does not hold give `{name}0`, `{name}1`, ...
    pub fn mint(&mut self, name: &str) -> String {
        let stem = if reads_as_resolved_anonymous(&format!("{name}0")) {
            format!("{name}_")
        } else {
            name.to_owned()
        };
        let next = self.next.entry(stem.clone()).or_insert(0);
        // Invariant: every `{stem}{m}` with `m < *next` was tried before and is reserved;
        // `names` is finite, so an unreserved name is found within `names.len() + 1` tries.
        loop {
            let candidate = format!("{stem}{next}");
            *next += 1;
            if self.names.insert(candidate.clone()) {
                return candidate;
            }
        }
    }
}

impl<S: Into<String>> FromIterator<S> for Reservation {
    fn from_iter<I: IntoIterator<Item = S>>(names: I) -> Self {
        let mut reservation = Self::new();
        reservation.extend(names);
        reservation
    }
}

impl<S: Into<String>> Extend<S> for Reservation {
    fn extend<I: IntoIterator<Item = S>>(&mut self, names: I) {
        self.names.extend(names.into_iter().map(Into::into));
    }
}

/// Whether `name` has the spelling `resolve anonymous variables` and kompile's other passes give
/// the variables they introduce for anonymous ones: `_Gen`, `?_Gen`, `!_Gen`, `@_Gen` or
/// `_DotVar` followed by one or more digits. Mints avoid it while passes still read it.
pub(crate) fn reads_as_resolved_anonymous(name: &str) -> bool {
    ["_Gen", "?_Gen", "!_Gen", "@_Gen", "_DotVar"]
        .iter()
        .any(|prefix| {
            name.strip_prefix(prefix).is_some_and(|suffix| {
                !suffix.is_empty() && suffix.bytes().all(|byte| byte.is_ascii_digit())
            })
        })
}

/// Rename the bound variables of one sentence apart, given its term-bearing fields (as
/// `Sentence::terms_mut` lists them): afterwards no name is bound by two quantifiers, and no
/// bound name is free in any of the terms.
///
/// In preorder over the terms in order, a quantifier keeps a name that is free in none of the
/// terms and that no earlier quantifier binds, and renames every other to a fresh name (module
/// documentation, "Fresh names"). `reserved` holds the names the new names must also avoid; the
/// names of the terms and the new names are added to it.
/// Returns each renaming in the order made, the old name and the new one.
///
/// Each term stays alpha-equivalent to its input, and terms already apart are left unchanged.
pub fn rename_apart_in_sentence<'a>(
    terms: impl IntoIterator<Item = &'a mut Term>,
    reserved: &mut Reservation,
) -> Vec<(String, String)> {
    let mut terms: Vec<&mut Term> = terms.into_iter().collect();
    let mut free = BTreeSet::new();
    for term in &terms {
        reserved.reserve_names_of(term);
        free.extend(free_variables(term));
    }
    let mut kept = BTreeSet::new();
    let mut renamed = Vec::new();
    for term in &mut terms {
        rename_bound(term, &mut |name| {
            if !free.contains(name) && kept.insert(name.to_owned()) {
                return None;
            }
            let new = reserved.mint(name);
            renamed.push((name.to_owned(), new.clone()));
            Some(new)
        });
    }
    renamed
}

/// Replace, in `term`, every free occurrence of each name of `map` by its term, all at once.
///
/// A quantifier that binds a name free in the replacement of a name free in its body first
/// renames that bound variable to a fresh name (module documentation, "Fresh names"), so that
/// the replacement's variable is not captured; no other bound variable is renamed.
/// `reserved` holds the names the new names must also avoid; the names of `term`, of the
/// replacements and of the keys, and the new names, are added to it. Reserving the keys keeps a
/// new name from being a key that does not occur in `term`, which would then replace the
/// occurrences just renamed.
/// A replacement takes the place of the whole occurrence, its annotations included.
/// A key that is an unresolved anonymous name names no single variable, so it replaces nothing.
///
/// The result is alpha-equivalent to the substitution of the replacements into `term` that
/// respects binding. It need not be apart: a replacement holding a quantifier is copied to each
/// occurrence, so its bound names can be bound twice, or be free elsewhere in the sentence. A
/// caller that must keep a sentence's bound names unique reserves the whole destination
/// sentence, the names its attributes mention included, before substituting, and renames the
/// sentence apart ([`rename_apart_in_sentence`]) afterwards.
pub fn substitute(term: &mut Term, map: &BTreeMap<String, Term>, reserved: &mut Reservation) {
    reserved.reserve_names_of(term);
    for (key, replacement) in map {
        reserved.reserve(key.clone());
        reserved.reserve_names_of(replacement);
    }
    let active: BTreeMap<&str, &Term> = map
        .iter()
        .filter(|(name, _)| !is_unresolved_anonymous(name))
        .map(|(name, replacement)| (name.as_str(), replacement))
        .collect();
    if active.is_empty() {
        return;
    }
    let free_in: BTreeMap<&str, BTreeSet<String>> = active
        .iter()
        .map(|(name, replacement)| (*name, free_variables(replacement)))
        .collect();
    substitute_in(term, &active, &free_in, reserved);
}

/// The binder and the body of `node`, an unannotated node, when it is a quantifier.
fn quantifier_mut(node: &mut Term) -> Option<(&mut Term, &mut Term)> {
    let Term::Apply { label, arguments } = node else {
        return None;
    };
    quantifier_kind(label)?;
    let [binder, body] = arguments.as_mut_slice() else {
        return None;
    };
    Some((binder, body))
}

fn unannotated_mut(term: &mut Term) -> &mut Term {
    let mut term = term;
    // Invariant: `term` is the original term with the annotations above it removed.
    while let Term::Annotated { term: inner, .. } = term {
        term = inner;
    }
    term
}

/// Call `visit` on the name of each variable of `binder` that a quantifier binds, in preorder.
fn for_each_bound_variable(binder: &mut Term, visit: &mut impl FnMut(&mut String)) {
    let mut pending = vec![binder];
    // Invariant: the variables of the nodes visited so far were passed to `visit` in preorder,
    // and `pending` holds the unvisited nodes, the next on top; each pop visits one node.
    while let Some(node) = pending.pop() {
        let node = unannotated_mut(node);
        if let Term::Variable { name, .. } = node {
            if !is_unresolved_anonymous(name) {
                visit(name);
            }
            continue;
        }
        pending.extend(node.children_mut().into_iter().rev());
    }
}

/// The distinct names `binder` binds, in preorder.
fn binder_names(binder: &mut Term) -> Vec<String> {
    let mut names: Vec<String> = Vec::new();
    for_each_bound_variable(binder, &mut |name| {
        if !names.contains(name) {
            names.push(name.clone());
        }
    });
    names
}

/// Give each variable of `binder` named by a key of `renames` its new name.
fn rename_binder(binder: &mut Term, renames: &BTreeMap<String, String>) {
    if renames.is_empty() {
        return;
    }
    for_each_bound_variable(binder, &mut |name| {
        if let Some(new) = renames.get(name.as_str()) {
            name.clone_from(new);
        }
    });
}

/// The renamings in force at a subterm, innermost last: a bound name with the name it takes, or
/// `None` where a quantifier binds the name again and keeps it.
type Renamings = Vec<(String, Option<String>)>;

// Invariant: each call visits one node of `term` and recurses only into its direct subterms (into
// a quantifier's body, not its binder), so the finite `term` bounds the calls; `scope` is the same
// on return as on entry.
fn rename_in(
    term: &mut Term,
    scope: &mut Renamings,
    rename: &mut impl FnMut(&str) -> Option<String>,
) {
    crate::stack::guarded(|| {
        let node = unannotated_mut(term);
        if let Some((binder, body)) = quantifier_mut(node) {
            let depth = scope.len();
            let mut renames = BTreeMap::new();
            for name in binder_names(binder) {
                let new = rename(&name);
                scope.push((name.clone(), new.clone()));
                if let Some(new) = new {
                    renames.insert(name, new);
                }
            }
            rename_binder(binder, &renames);
            rename_in(body, scope, rename);
            scope.truncate(depth);
            return;
        }
        match node {
            Term::Variable { name, .. } => {
                if let Some((_, Some(new))) = scope.iter().rev().find(|(old, _)| old == name) {
                    name.clone_from(new);
                }
            }
            Term::InjectedLabel(_) | Term::Token { .. } => {}
            Term::Rewrite { .. } | Term::As { .. } | Term::Sequence(_) | Term::Apply { .. } => {
                for child in node.children_mut() {
                    rename_in(child, scope, rename);
                }
            }
            Term::Annotated { .. } => unreachable!("unannotated_mut strips annotations"),
        }
    });
}

// Invariant: each call visits one node of `term` and recurses only into its direct subterms (into
// a quantifier's body, not its binder), never into a replacement it has put in place, so the
// finite `term` bounds the calls; `active` maps each name to replace below `term` to its
// replacement, and `free_in` each key of `active` to its replacement's free names.
fn substitute_in(
    term: &mut Term,
    active: &BTreeMap<&str, &Term>,
    free_in: &BTreeMap<&str, BTreeSet<String>>,
    reserved: &mut Reservation,
) {
    crate::stack::guarded(|| {
        if let Term::Variable { name, .. } = term.unannotated()
            && let Some(replacement) = active.get(name.as_str())
        {
            *term = (*replacement).clone();
            return;
        }
        let node = unannotated_mut(term);
        if let Some((binder, body)) = quantifier_mut(node) {
            let names = binder_names(binder);
            let mut inner = active.clone();
            for name in &names {
                inner.remove(name.as_str());
            }
            if inner.is_empty() {
                return;
            }
            if names
                .iter()
                .any(|name| inner.keys().any(|key| free_in[key].contains(name)))
            {
                let body_free = free_variables(body);
                let mut renames = BTreeMap::new();
                for name in names {
                    let captures = inner
                        .keys()
                        .any(|key| body_free.contains(*key) && free_in[key].contains(&name));
                    if captures {
                        let new = reserved.mint(&name);
                        renames.insert(name, new);
                    }
                }
                if !renames.is_empty() {
                    rename_binder(binder, &renames);
                    let mut scope = renames
                        .into_iter()
                        .map(|(old, new)| (old, Some(new)))
                        .collect();
                    rename_in(body, &mut scope, &mut |_| None);
                }
            }
            substitute_in(body, &inner, free_in, reserved);
            return;
        }
        match node {
            Term::Variable { .. } | Term::InjectedLabel(_) | Term::Token { .. } => {}
            Term::Rewrite { .. } | Term::As { .. } | Term::Sequence(_) | Term::Apply { .. } => {
                for child in node.children_mut() {
                    substitute_in(child, active, free_in, reserved);
                }
            }
            Term::Annotated { .. } => unreachable!("unannotated_mut strips annotations"),
        }
    });
}

#[cfg(test)]
mod tests {
    //! The operations are checked against a locally nameless reference ([`Nameless`]): a bound
    //! occurrence is the number of quantifiers between it and its binder, so alpha-equivalent
    //! terms have equal forms, and substitution for a free name renames nothing. The oracle
    //! recognises binders by its own reading of the rule and shares no code with the module.
    //!
    //! The properties run `KAST_BINDING_CASES` cases (256 by default) and the census
    //! `KAST_BINDING_CENSUS` draws (1,024 by default), all from fixed seeds, so a run is
    //! reproducible; `scripts/alpha-invariance.sh` runs both at 50,000.

    use std::collections::{BTreeMap, BTreeSet};

    use proptest::prelude::*;
    use proptest::test_runner::RngSeed;

    use super::{
        QuantifierKind, Reservation, Role, bound_names, free_variables, occurrences, quantifier,
        rename_apart_in_sentence, rename_bound, substitute,
    };
    use crate::kast::{Label, Sort, Term, TermMetadata};

    /// The seed of every property and of the census.
    const SEED: u64 = 0x6b61_7374_6269_6e64;

    fn from_environment(variable: &str, default: u32) -> u32 {
        std::env::var(variable)
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(default)
    }

    fn config() -> ProptestConfig {
        ProptestConfig {
            cases: from_environment("KAST_BINDING_CASES", 256),
            rng_seed: RngSeed::Fixed(SEED),
            failure_persistence: None,
            ..ProptestConfig::default()
        }
    }

    // ------------------------------------------------------------------ the reference oracle

    /// A term in locally nameless form.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Nameless {
        Free {
            name: String,
            sort: Option<Sort>,
        },
        /// `index` quantifiers lie between the occurrence and its binder, which binds it as the
        /// `position`-th distinct name of the binder.
        Bound {
            index: usize,
            position: usize,
            sort: Option<Sort>,
        },
        /// A variable of a binder: the binder's `position`-th distinct name, with its sigil and
        /// `_` prefix.
        Binding {
            position: usize,
            sort: Option<Sort>,
            sigil: Option<char>,
            underscore: bool,
        },
        /// An anonymous variable as written in a binder, which binds nothing.
        Anonymous {
            name: String,
            sort: Option<Sort>,
        },
        Quantifier {
            label: Label,
            binder: Box<Nameless>,
            body: Box<Nameless>,
        },
        Node {
            head: Head,
            children: Vec<Nameless>,
        },
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Head {
        InjectedLabel(Label),
        Rewrite,
        As,
        Sequence,
        Apply(Label),
        Token(String, Sort),
    }

    fn written_anonymous(name: &str) -> bool {
        ["_", "?_", "!_", "@_"].contains(&name)
    }

    /// The quantifier `term` is to the oracle: `#Exists` or `#Forall` of two arguments.
    fn oracle_quantifier(term: &Term) -> Option<(&Label, &Term, &Term)> {
        match term.unannotated() {
            Term::Apply { label, arguments }
                if ["#Exists", "#Forall"].contains(&label.name.as_str())
                    && arguments.len() == 2 =>
            {
                Some((label, &arguments[0], &arguments[1]))
            }
            Term::Apply { .. }
            | Term::InjectedLabel(_)
            | Term::Rewrite { .. }
            | Term::As { .. }
            | Term::Variable { .. }
            | Term::Sequence(_)
            | Term::Token { .. }
            | Term::Annotated { .. } => None,
        }
    }

    /// The structure of a node other than its children.
    fn head(term: &Term) -> Head {
        match term.unannotated() {
            Term::InjectedLabel(label) => Head::InjectedLabel(label.clone()),
            Term::Rewrite { .. } => Head::Rewrite,
            Term::As { .. } => Head::As,
            Term::Sequence(_) => Head::Sequence,
            Term::Apply { label, .. } => Head::Apply(label.clone()),
            Term::Token { token, sort } => Head::Token(token.clone(), sort.clone()),
            Term::Variable { .. } | Term::Annotated { .. } => {
                unreachable!("a variable has no head and unannotated strips annotations")
            }
        }
    }

    /// A binder without its names; `names` collects the distinct names it binds, in preorder.
    fn binder_form(binder: &Term, names: &mut Vec<String>) -> Nameless {
        if let Term::Variable { name, sort } = binder.unannotated() {
            if written_anonymous(name) {
                return Nameless::Anonymous {
                    name: name.clone(),
                    sort: sort.clone(),
                };
            }
            let position = names
                .iter()
                .position(|bound| bound == name)
                .unwrap_or_else(|| {
                    names.push(name.clone());
                    names.len() - 1
                });
            let sigil = name.chars().next().filter(|first| "?!@".contains(*first));
            let rest = &name[sigil.map_or(0, char::len_utf8)..];
            return Nameless::Binding {
                position,
                sort: sort.clone(),
                sigil,
                underscore: rest.starts_with('_'),
            };
        }
        Nameless::Node {
            head: head(binder),
            children: binder
                .children()
                .into_iter()
                .map(|child| binder_form(child, names))
                .collect(),
        }
    }

    /// `term` in locally nameless form, under the binders `scope` (innermost last, each with the
    /// names it binds).
    fn nameless(term: &Term, scope: &mut Vec<Vec<String>>) -> Nameless {
        if let Some((label, binder, body)) = oracle_quantifier(term) {
            let mut names = Vec::new();
            let binder = binder_form(binder, &mut names);
            scope.push(names);
            let body = nameless(body, scope);
            scope.pop();
            return Nameless::Quantifier {
                label: label.clone(),
                binder: Box::new(binder),
                body: Box::new(body),
            };
        }
        if let Term::Variable { name, sort } = term.unannotated() {
            for (index, names) in scope.iter().rev().enumerate() {
                if let Some(position) = names.iter().position(|bound| bound == name) {
                    return Nameless::Bound {
                        index,
                        position,
                        sort: sort.clone(),
                    };
                }
            }
            return Nameless::Free {
                name: name.clone(),
                sort: sort.clone(),
            };
        }
        Nameless::Node {
            head: head(term),
            children: term
                .children()
                .into_iter()
                .map(|child| nameless(child, scope))
                .collect(),
        }
    }

    fn closed(term: &Term) -> Nameless {
        nameless(term, &mut Vec::new())
    }

    fn oracle_free(form: &Nameless, free: &mut BTreeSet<String>) {
        match form {
            Nameless::Free { name, .. } => {
                free.insert(name.clone());
            }
            Nameless::Bound { .. } | Nameless::Binding { .. } | Nameless::Anonymous { .. } => {}
            Nameless::Quantifier { body, .. } => oracle_free(body, free),
            Nameless::Node { children, .. } => {
                for child in children {
                    oracle_free(child, free);
                }
            }
        }
    }

    /// The names the quantifiers of `term` bind, in preorder.
    fn oracle_bound(term: &Term, names: &mut Vec<String>) {
        if let Some((_, binder, body)) = oracle_quantifier(term) {
            let mut own = Vec::new();
            binder_form(binder, &mut own);
            names.extend(own);
            oracle_bound(body, names);
        } else {
            for child in term.children() {
                oracle_bound(child, names);
            }
        }
    }

    /// The role of each variable occurrence of a nameless form, in preorder, with the name of
    /// each free one: a bound occurrence's quantifier is the one `index` steps out on the path
    /// to it, and the quantifiers are numbered in preorder.
    fn nameless_roles(
        form: &Nameless,
        path: &mut Vec<usize>,
        quantifiers: &mut usize,
        roles: &mut Vec<(Role, Option<String>)>,
    ) {
        fn binder_roles(form: &Nameless, number: usize, roles: &mut Vec<(Role, Option<String>)>) {
            match form {
                Nameless::Binding { .. } | Nameless::Anonymous { .. } => {
                    roles.push((Role::Binding { binder: number }, None));
                }
                Nameless::Node { children, .. } => {
                    for child in children {
                        binder_roles(child, number, roles);
                    }
                }
                Nameless::Free { .. } | Nameless::Bound { .. } | Nameless::Quantifier { .. } => {
                    unreachable!("a binder form holds bindings and nodes")
                }
            }
        }
        match form {
            Nameless::Free { name, .. } => roles.push((Role::Free, Some(name.clone()))),
            Nameless::Bound { index, .. } => roles.push((
                Role::Bound {
                    binder: path[path.len() - 1 - index],
                },
                None,
            )),
            Nameless::Binding { .. } | Nameless::Anonymous { .. } => {
                unreachable!("bindings are visited with their quantifier")
            }
            Nameless::Quantifier { binder, body, .. } => {
                let number = *quantifiers;
                *quantifiers += 1;
                binder_roles(binder, number, roles);
                path.push(number);
                nameless_roles(body, path, quantifiers, roles);
                path.pop();
            }
            Nameless::Node { children, .. } => {
                for child in children {
                    nameless_roles(child, path, quantifiers, roles);
                }
            }
        }
    }

    /// Substitution in locally nameless form: a replacement is locally closed, so it takes the
    /// place of a free occurrence as it is.
    fn oracle_substitute(form: &Nameless, map: &BTreeMap<String, Nameless>) -> Nameless {
        match form {
            Nameless::Free { name, .. } if !written_anonymous(name) && map.contains_key(name) => {
                map[name].clone()
            }
            Nameless::Free { .. }
            | Nameless::Bound { .. }
            | Nameless::Binding { .. }
            | Nameless::Anonymous { .. } => form.clone(),
            Nameless::Quantifier {
                label,
                binder,
                body,
            } => Nameless::Quantifier {
                label: label.clone(),
                binder: binder.clone(),
                body: Box::new(oracle_substitute(body, map)),
            },
            Nameless::Node { head, children } => Nameless::Node {
                head: head.clone(),
                children: children
                    .iter()
                    .map(|child| oracle_substitute(child, map))
                    .collect(),
            },
        }
    }

    /// Substitution that respects binding but renames nothing, keeping every annotation: right
    /// exactly when no binder would capture a replacement's variable.
    fn substitute_without_renaming(term: &Term, map: &BTreeMap<String, Term>) -> Term {
        if let Term::Variable { name, .. } = term.unannotated()
            && !written_anonymous(name)
            && let Some(replacement) = map.get(name)
        {
            return replacement.clone();
        }
        let mut copy = term.clone();
        if let Some((_, binder, body)) = oracle_quantifier(term) {
            let mut names = Vec::new();
            binder_form(binder, &mut names);
            let mut inner = map.clone();
            for name in names {
                inner.remove(&name);
            }
            *copy.children_mut()[1] = substitute_without_renaming(body, &inner);
            return copy;
        }
        for (child, original) in copy.children_mut().into_iter().zip(term.children()) {
            *child = substitute_without_renaming(original, map);
        }
        copy
    }

    /// C1's free-variable walk as it stood before the port (`invariants/stage.rs:423-470` at
    /// 9f7ef193c), kept to show that the module gives the same answer.
    fn c1_free_variables(term: &Term) -> BTreeSet<String> {
        let mut free = BTreeSet::new();
        let mut bound: Vec<String> = Vec::new();
        let mut pending: Vec<(&Term, usize)> = vec![(term, 0)];
        // Invariant: as in the original.
        while let Some((node, scope)) = pending.pop() {
            bound.truncate(scope);
            match node.unannotated() {
                Term::Variable { name, .. } => {
                    if !bound.contains(name) {
                        free.insert(name.clone());
                    }
                }
                Term::Apply { label, arguments }
                    if (label.name == "#Exists" || label.name == "#Forall")
                        && arguments.len() == 2 =>
                {
                    arguments[0].visit_preorder(&mut |binder| {
                        if let Term::Variable { name, .. } = binder.unannotated()
                            && !written_anonymous(name)
                        {
                            bound.push(name.clone());
                        }
                    });
                    pending.push((&arguments[1], bound.len()));
                }
                other @ (Term::InjectedLabel(_)
                | Term::Rewrite { .. }
                | Term::As { .. }
                | Term::Sequence(_)
                | Term::Apply { .. }
                | Term::Token { .. }
                | Term::Annotated { .. }) => {
                    for child in other.children() {
                        pending.push((child, scope));
                    }
                }
            }
        }
        free
    }

    /// Whether `left` and `right` carry identical annotations at every node, the same number of
    /// children everywhere; names and labels are compared elsewhere.
    fn same_annotations(left: &Term, right: &Term) -> bool {
        match (left, right) {
            (
                Term::Annotated {
                    term: left,
                    metadata: left_metadata,
                },
                Term::Annotated {
                    term: right,
                    metadata: right_metadata,
                },
            ) => left_metadata.identical(right_metadata) && same_annotations(left, right),
            (Term::Annotated { .. }, _) | (_, Term::Annotated { .. }) => false,
            _ => {
                let (left, right) = (left.children(), right.children());
                left.len() == right.len()
                    && left
                        .into_iter()
                        .zip(right)
                        .all(|(left, right)| same_annotations(left, right))
            }
        }
    }

    fn names_of(term: &Term) -> BTreeSet<String> {
        let mut names = BTreeSet::new();
        term.visit_preorder(&mut |node| {
            if let Term::Variable { name, .. } = node {
                names.insert(name.clone());
            }
        });
        names
    }

    /// Whether `terms` are apart: no name bound twice, and no bound name free in any of them.
    fn apart(terms: &[Term]) -> bool {
        let bound: Vec<String> = terms.iter().flat_map(bound_names).collect();
        let distinct: BTreeSet<&String> = bound.iter().collect();
        let free: BTreeSet<String> = terms.iter().flat_map(free_variables).collect();
        distinct.len() == bound.len() && distinct.iter().all(|name| !free.contains(*name))
    }

    fn binds_a_name_twice(term: &Term) -> bool {
        let bound = bound_names(term);
        bound.iter().collect::<BTreeSet<_>>().len() < bound.len()
    }

    // ------------------------------------------------------------------ generators

    /// Names that collide with the fresh names (`X0`, `Y0`) and carry each spelling class; the
    /// first seven are not anonymous.
    const NAMES: [&str; 9] = ["X", "Y", "Z", "X0", "Y0", "?X", "_A", "_", "?_"];

    fn name() -> impl Strategy<Value = String> {
        prop::sample::select(&NAMES[..]).prop_map(str::to_owned)
    }

    fn named() -> impl Strategy<Value = String> {
        prop::sample::select(&NAMES[..7]).prop_map(str::to_owned)
    }

    /// `count` distinct names that are not anonymous, in random order.
    fn distinct_names(count: usize) -> impl Strategy<Value = Vec<String>> {
        prop::sample::subsequence(&NAMES[..7], count)
            .prop_shuffle()
            .prop_map(|names| names.into_iter().map(str::to_owned).collect())
    }

    fn sort() -> impl Strategy<Value = Option<Sort>> {
        prop_oneof![
            Just(None),
            Just(Some(Sort::new("Int"))),
            Just(Some(Sort::new("Bool"))),
        ]
    }

    /// `term` annotated with a metadata sort that `mark` distinguishes, so a moved annotation is
    /// told apart from a kept one.
    fn annotated(term: Term, mark: u8) -> Term {
        term.with_metadata(TermMetadata {
            sort: Some(Sort::new(format!("K{mark}"))),
            ..TermMetadata::default()
        })
    }

    fn variable() -> impl Strategy<Value = Term> {
        (name(), sort()).prop_map(|(name, sort)| Term::Variable { name, sort })
    }

    fn annotated_variable() -> impl Strategy<Value = Term> {
        (variable(), any::<u8>()).prop_map(|(variable, mark)| annotated(variable, mark))
    }

    /// A binder: a variable, annotated or not, under a semantic cast or not; a token; or a
    /// malformed application holding two variables.
    fn binder() -> impl Strategy<Value = Term> {
        prop_oneof![
            4 => variable(),
            1 => annotated_variable(),
            1 => variable().prop_map(|variable| Term::apply("#SemanticCastToInt", vec![variable])),
            1 => Just(Term::Token {
                token: "1".into(),
                sort: Sort::new("Int"),
            }),
            1 => (variable(), variable()).prop_map(|(left, right)| Term::apply("f", vec![left, right])),
        ]
    }

    fn quantified(kind: QuantifierKind, binder: Term, body: Term) -> Term {
        let name = match kind {
            QuantifierKind::Exists => "#Exists",
            QuantifierKind::Forall => "#Forall",
        };
        Term::Apply {
            label: Label::with_parameters(name, vec![Sort::new("Int"), Sort::new("Bool")]),
            arguments: vec![binder, body],
        }
    }

    fn kind() -> impl Strategy<Value = QuantifierKind> {
        prop_oneof![Just(QuantifierKind::Exists), Just(QuantifierKind::Forall)]
    }

    /// Terms of up to four levels over every constructor, mostly quantifiers of both kinds and
    /// applications, with annotations, and `#Exists` applied to a number of arguments other than
    /// two.
    fn term() -> BoxedStrategy<Term> {
        term_of_depth(4)
    }

    fn term_of_depth(depth: u32) -> BoxedStrategy<Term> {
        let leaf = prop_oneof![
            5 => variable(),
            1 => annotated_variable(),
            1 => Just(Term::Token {
                token: "0".into(),
                sort: Sort::new("Int"),
            }),
            1 => Just(Term::InjectedLabel(Label::new("l"))),
            1 => Just(Term::apply("c", Vec::new())),
        ]
        .boxed();
        let Some(below) = depth.checked_sub(1) else {
            return leaf;
        };
        let inner = term_of_depth(below);
        prop_oneof![
            2 => leaf,
            5 => (kind(), binder(), inner.clone())
                .prop_map(|(kind, binder, body)| quantified(kind, binder, body)),
            4 => (prop::sample::select(&["f", "g"][..]), prop::collection::vec(inner.clone(), 1..3))
                .prop_map(|(label, arguments)| Term::apply(label, arguments)),
            1 => (inner.clone(), inner.clone()).prop_map(|(left, right)| Term::Rewrite {
                left: Box::new(left),
                right: Box::new(right),
            }),
            1 => (inner.clone(), inner.clone()).prop_map(|(pattern, alias)| Term::As {
                pattern: Box::new(pattern),
                alias: Box::new(alias),
            }),
            1 => prop::collection::vec(inner.clone(), 0..3).prop_map(Term::Sequence),
            1 => (inner.clone(), any::<u8>()).prop_map(|(term, mark)| annotated(term, mark)),
            1 => (prop::sample::select(&[0_usize, 1, 3][..]), prop::collection::vec(inner, 3))
                .prop_map(|(arity, mut arguments)| {
                    arguments.truncate(arity);
                    Term::apply("#Exists", arguments)
                }),
        ]
        .boxed()
    }

    fn substitution() -> impl Strategy<Value = BTreeMap<String, Term>> {
        prop::collection::btree_map(name(), term_of_depth(2), 1..4)
    }

    /// A term, or one in which a quantifier over `B` holds another over `B` around an
    /// occurrence of `B`.
    fn term_with_shadowing() -> impl Strategy<Value = Term> {
        let shadowing = (kind(), named(), term_of_depth(2), term_of_depth(2)).prop_map(
            |(kind, binder, beside, body)| {
                let inner = quantified(
                    kind,
                    Term::variable(binder.clone()),
                    Term::apply("f", vec![Term::variable(binder.clone()), body]),
                );
                quantified(
                    kind,
                    Term::variable(binder.clone()),
                    Term::apply("g", vec![Term::variable(binder), beside, inner]),
                )
            },
        );
        prop_oneof![term(), shadowing]
    }

    fn v(name: &str) -> Term {
        Term::variable(name)
    }

    fn f(arguments: Vec<Term>) -> Term {
        Term::apply("f", arguments)
    }

    fn g(arguments: Vec<Term>) -> Term {
        Term::apply("g", arguments)
    }

    /// A term and a substitution, from five families:
    /// - both drawn independently;
    /// - capture: a quantifier over `B` around a free `K`, with `K` replaced by a term in which
    ///   `B` is free, so the quantifier must rename `B`;
    /// - the same with a key `{B}0` that the term does not hold, the name a rename of `B` would
    ///   take if the keys were not reserved;
    /// - a chain: `K1` replaced by a term holding `K2` and `B`, `K2` free beside the quantifier
    ///   and replaced in turn, so the substitution must be simultaneous and still rename `B`;
    /// - capture in a term that binds `B` twice, one quantifier inside the other.
    fn substitution_case() -> impl Strategy<Value = (Term, BTreeMap<String, Term>)> {
        let capturing = (
            kind(),
            distinct_names(2),
            term_of_depth(2),
            term_of_depth(2),
            term_of_depth(1),
            substitution(),
        )
            .prop_map(|(kind, names, beside, body, rest, mut map)| {
                let (binder, key) = (&names[0], &names[1]);
                let body = f(vec![v(key), body]);
                let term = g(vec![beside, quantified(kind, v(binder), body)]);
                map.insert(key.clone(), f(vec![v(binder), rest]));
                (term, map)
            });
        let absent_key = (
            kind(),
            distinct_names(2),
            term_of_depth(1),
            term_of_depth(1),
            term_of_depth(1),
            substitution(),
        )
            .prop_map(|(kind, names, beside, body, rest, mut map)| {
                let (binder, key) = (&names[0], &names[1]);
                let body = f(vec![v(key), v(binder), body]);
                let term = g(vec![beside, quantified(kind, v(binder), body)]);
                map.insert(key.clone(), f(vec![v(binder), rest]));
                map.insert(format!("{binder}0"), Term::apply("c", Vec::new()));
                (term, map)
            });
        let chain = (
            kind(),
            distinct_names(3),
            term_of_depth(2),
            term_of_depth(2),
            term_of_depth(1),
            term_of_depth(1),
            substitution(),
        )
            .prop_map(|(kind, names, beside, body, first, second, mut map)| {
                let (binder, key, next) = (&names[0], &names[1], &names[2]);
                let quantifier = quantified(kind, v(binder), f(vec![v(key), body]));
                let term = g(vec![v(next), beside, quantifier]);
                map.insert(key.clone(), f(vec![v(next), v(binder), first]));
                map.insert(next.clone(), f(vec![v(binder), second]));
                (term, map)
            });
        let shadowed = (
            kind(),
            distinct_names(2),
            term_of_depth(2),
            term_of_depth(2),
            term_of_depth(1),
            substitution(),
        )
            .prop_map(|(kind, names, beside, body, rest, mut map)| {
                let (binder, key) = (&names[0], &names[1]);
                let inner = quantified(kind, v(binder), f(vec![v(key), v(binder), body]));
                let term = quantified(kind, v(binder), g(vec![v(binder), beside, inner]));
                map.insert(key.clone(), f(vec![v(binder), rest]));
                (term, map)
            });
        prop_oneof![
            1 => (term(), substitution()),
            1 => capturing,
            1 => absent_key,
            2 => chain,
            2 => shadowed,
        ]
    }

    /// `term` with each binder `rename_bound` asks about renamed where `choices` says so (cycling)
    /// to its name followed by `F<i>`, a name no generated term holds, of the same sigil and `_`
    /// prefix; with the renamings made.
    fn renamed_to_fresh(term: &Term, choices: &[bool]) -> (Term, Vec<(String, String)>) {
        let mut renamed = term.clone();
        let mut made = Vec::new();
        let mut asked = 0_usize;
        rename_bound(&mut renamed, &mut |name| {
            let choose = choices.is_empty() || choices[asked % choices.len()];
            asked += 1;
            choose.then(|| {
                let new = format!("{name}F{}", made.len());
                made.push((name.to_owned(), new.clone()));
                new
            })
        });
        (renamed, made)
    }

    // ------------------------------------------------------------------ properties

    proptest! {
        #![proptest_config(config())]

        /// The free names are the oracle's, and C1's before the port.
        #[test]
        fn free_variables_are_the_free_names_of_the_nameless_form(term in term()) {
            let mut expected = BTreeSet::new();
            oracle_free(&closed(&term), &mut expected);
            prop_assert_eq!(free_variables(&term), expected);
            prop_assert_eq!(free_variables(&term), c1_free_variables(&term));
        }

        /// `bound_names` lists each quantifier's distinct bound names, in preorder.
        #[test]
        fn bound_names_list_every_binding_in_preorder(term in term_with_shadowing()) {
            let mut expected = Vec::new();
            oracle_bound(&term, &mut expected);
            prop_assert_eq!(bound_names(&term), expected);
        }

        /// `occurrences` gives each variable occurrence in preorder with the role the nameless
        /// form gives it: free with its name, bound by the quantifier its index points to, or a
        /// binder's own; each node is the stored occurrence, and a bound occurrence has a name
        /// its quantifier's binder holds.
        #[test]
        fn occurrences_are_the_roles_of_the_nameless_form(term in term_with_shadowing()) {
            let found = occurrences(&term);
            let mut expected = Vec::new();
            nameless_roles(&closed(&term), &mut Vec::new(), &mut 0, &mut expected);
            let roles: Vec<(Role, Option<String>)> = found
                .iter()
                .map(|occurrence| {
                    let name = (occurrence.role == Role::Free).then(|| occurrence.name.to_owned());
                    (occurrence.role, name)
                })
                .collect();
            prop_assert_eq!(roles, expected);
            let free: BTreeSet<String> = found
                .iter()
                .filter(|occurrence| occurrence.role == Role::Free)
                .map(|occurrence| occurrence.name.to_owned())
                .collect();
            prop_assert_eq!(free, free_variables(&term));
            for occurrence in &found {
                let Term::Variable { name, sort } = occurrence.node.unannotated() else {
                    return Err(TestCaseError::fail("an occurrence is a variable node"));
                };
                prop_assert_eq!((name.as_str(), sort.as_ref()), (occurrence.name, occurrence.sort));
                if let Role::Bound { binder } = occurrence.role {
                    let held = found.iter().any(|other| {
                        other.role == Role::Binding { binder } && other.name == occurrence.name
                    });
                    prop_assert!(held, "a bound occurrence's name is its binder's");
                }
            }
        }

        /// Renaming any choice of bound variables to unused names keeps the term alpha-equivalent,
        /// keeps every annotation, renames exactly the chosen bindings, keeps the free names, and
        /// is undone by the inverse renaming.
        #[test]
        fn renaming_bound_variables_to_unused_names_is_an_alpha_conversion(
            term in term_with_shadowing(),
            choices in prop::collection::vec(any::<bool>(), 0..8),
        ) {
            let (renamed, made) = renamed_to_fresh(&term, &choices);
            prop_assert_eq!(closed(&renamed), closed(&term));
            prop_assert!(same_annotations(&renamed, &term));
            prop_assert_eq!(free_variables(&renamed), free_variables(&term));
            let mut made_iter = made.iter();
            let mut renamed_names = bound_names(&renamed).into_iter();
            for original in bound_names(&term) {
                let now = renamed_names.next().expect("as many bindings");
                if now == original {
                    continue;
                }
                let (old, new) = made_iter.next().expect("a renaming for each changed binding");
                prop_assert_eq!((old, new), (&original, &now));
            }
            prop_assert!(made_iter.next().is_none());
            let inverse: BTreeMap<String, String> =
                made.iter().map(|(old, new)| (new.clone(), old.clone())).collect();
            let mut restored = renamed.clone();
            rename_bound(&mut restored, &mut |name| inverse.get(name).cloned());
            prop_assert_eq!(restored, term);
        }

        /// Renaming a sentence apart keeps each term alpha-equivalent and its annotations, leaves
        /// the terms apart, renames nothing in terms already apart, and reserves every name it
        /// meets or makes.
        #[test]
        fn renaming_a_sentence_apart_keeps_its_meaning_and_makes_it_apart(
            terms in prop::collection::vec(term_with_shadowing(), 1..4),
        ) {
            let mut renamed = terms.clone();
            let mut reserved: Reservation = ["W"].into_iter().collect();
            let renamings = rename_apart_in_sentence(renamed.iter_mut(), &mut reserved);
            for (before, after) in terms.iter().zip(&renamed) {
                prop_assert_eq!(closed(after), closed(before));
                prop_assert!(same_annotations(after, before));
                prop_assert!(names_of(before).is_subset(reserved.names()));
                prop_assert!(names_of(after).is_subset(reserved.names()));
            }
            prop_assert!(apart(&renamed));
            if apart(&terms) {
                prop_assert!(renamings.is_empty());
                prop_assert_eq!(&renamed, &terms);
            }
            let before: Vec<String> = terms.iter().flat_map(bound_names).collect();
            let after: Vec<String> = renamed.iter().flat_map(bound_names).collect();
            let changed: Vec<(String, String)> = before
                .into_iter()
                .zip(after)
                .filter(|(old, new)| old != new)
                .collect();
            prop_assert_eq!(&renamings, &changed);
            prop_assert!(renamings.iter().all(|(_, new)| new != "W"));
            let again = renamed.clone();
            prop_assert!(
                rename_apart_in_sentence(renamed.iter_mut(), &mut Reservation::new()).is_empty()
            );
            prop_assert_eq!(renamed, again);
        }

        /// Substitution agrees with substitution in locally nameless form, keeps the annotations
        /// of every node it does not replace, mints only names it reserves and that were not
        /// reserved before, and renames no binder where none would capture.
        #[test]
        fn substitution_is_the_nameless_substitution((term, map) in substitution_case()) {
            let mut result = term.clone();
            let before: Reservation = ["W"].into_iter().collect();
            let mut reserved = before.clone();
            substitute(&mut result, &map, &mut reserved);
            let forms: BTreeMap<String, Nameless> =
                map.iter().map(|(name, replacement)| (name.clone(), closed(replacement))).collect();
            prop_assert_eq!(closed(&result), oracle_substitute(&closed(&term), &forms));
            let unrenamed = substitute_without_renaming(&term, &map);
            prop_assert!(same_annotations(&result, &unrenamed));
            let mut met = names_of(&term);
            met.extend(map.keys().cloned());
            for replacement in map.values() {
                met.extend(names_of(replacement));
            }
            prop_assert!(met.is_subset(reserved.names()));
            for name in names_of(&result).difference(&met) {
                prop_assert!(reserved.contains(name) && !before.contains(name));
            }
            let replacement_free: BTreeSet<String> = map.values().flat_map(free_variables).collect();
            if bound_names(&term).iter().all(|name| !replacement_free.contains(name)) {
                prop_assert_eq!(result, unrenamed);
            }
        }
    }

    // ------------------------------------------------------------------ census

    /// Whether a replacement of a key free in `term` mentions another key free in `term`.
    fn is_chain(term: &Term, map: &BTreeMap<String, Term>) -> bool {
        let free = free_variables(term);
        map.iter().any(|(key, replacement)| {
            free.contains(key) && {
                let mentions = free_variables(replacement);
                map.keys()
                    .any(|other| other != key && free.contains(other) && mentions.contains(other))
            }
        })
    }

    /// Whether a key that `term` does not hold is spelled `{B}0` for a name `B` that `term`
    /// binds.
    fn has_absent_mint_key(term: &Term, map: &BTreeMap<String, Term>) -> bool {
        let names = names_of(term);
        let bound = bound_names(term);
        map.keys()
            .any(|key| !names.contains(key) && bound.iter().any(|name| *key == format!("{name}0")))
    }

    /// A fixed-seed census of the substitution cases: substitution never disagrees with the
    /// oracle, and the generators reach each case the properties are about in a stated share
    /// of draws. Its counts are printed for the gate's log.
    #[test]
    fn the_substitution_census_reaches_every_case_and_finds_no_disagreement() {
        use proptest::{
            strategy::ValueTree,
            test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
        };

        let draws = from_environment("KAST_BINDING_CENSUS", 1024);
        let mut runner = TestRunner::new_with_rng(
            Config::default(),
            TestRng::from_seed(RngAlgorithm::ChaCha, &[0x5a; 32]),
        );
        let (mut disagreements, mut captures, mut chains, mut shadowed, mut absent) =
            (0_u32, 0_u32, 0_u32, 0_u32, 0_u32);
        let (mut apart_renamings, mut shadowing) = (0_u32, 0_u32);
        let mut first_disagreement = None;
        let (cases, shadowing_terms) = (substitution_case(), term_with_shadowing());
        for _ in 0..draws {
            let (term, map) = cases.new_tree(&mut runner).expect("a case").current();
            let mut result = term.clone();
            substitute(&mut result, &map, &mut Reservation::new());
            let forms: BTreeMap<String, Nameless> = map
                .iter()
                .map(|(name, replacement)| (name.clone(), closed(replacement)))
                .collect();
            if closed(&result) != oracle_substitute(&closed(&term), &forms) {
                disagreements += 1;
                first_disagreement.get_or_insert_with(|| (term.clone(), map.clone()));
            }
            let capture = result != substitute_without_renaming(&term, &map);
            captures += u32::from(capture);
            chains += u32::from(is_chain(&term, &map));
            shadowed += u32::from(capture && binds_a_name_twice(&term));
            absent += u32::from(capture && has_absent_mint_key(&term, &map));
            let shadowing_term = shadowing_terms
                .new_tree(&mut runner)
                .expect("a term")
                .current();
            shadowing += u32::from(binds_a_name_twice(&shadowing_term));
            let mut renamed = shadowing_term;
            apart_renamings += u32::from(
                !rename_apart_in_sentence([&mut renamed], &mut Reservation::new()).is_empty(),
            );
        }
        let share = |count: u32| f64::from(count) / f64::from(draws);
        let counts = format!(
            "{draws} draws: {disagreements} disagreements; captures {captures} ({:.1}%), \
             chains {chains} ({:.1}%), captures in a term binding a name twice {shadowed} \
             ({:.1}%), captures beside an absent key spelled like a mint {absent} ({:.1}%); \
             shadowing terms {shadowing} ({:.1}%), renamed apart {apart_renamings} ({:.1}%)",
            100.0 * share(captures),
            100.0 * share(chains),
            100.0 * share(shadowed),
            100.0 * share(absent),
            100.0 * share(shadowing),
            100.0 * share(apart_renamings),
        );
        eprintln!("binding census: {counts}");
        assert_eq!(
            disagreements, 0,
            "{counts}; the first: {first_disagreement:?}"
        );
        assert!(
            share(captures) >= 0.5
                && share(chains) >= 0.25
                && share(shadowed) >= 0.25
                && share(absent) >= 0.1
                && share(shadowing) >= 0.25
                && share(apart_renamings) >= 0.25,
            "{counts}"
        );
    }

    // ------------------------------------------------------------------ examples

    fn exists(binder: Term, body: Term) -> Term {
        quantified(QuantifierKind::Exists, binder, body)
    }

    fn names(list: &[&str]) -> BTreeSet<String> {
        list.iter().map(|name| (*name).to_owned()).collect()
    }

    #[test]
    fn a_quantifier_is_exists_or_forall_of_two_arguments() {
        let term = annotated(exists(v("X"), f(vec![v("X")])), 0);
        let found = quantifier(&term).expect("a quantifier");
        assert_eq!(found.kind, QuantifierKind::Exists);
        assert_eq!(found.variable(), Some(("X", None)));
        assert_eq!(found.bound(), vec!["X"]);
        let cast = exists(
            Term::apply("#SemanticCastToInt", vec![v("X")]),
            f(vec![v("X")]),
        );
        let found = quantifier(&cast).expect("a quantifier");
        assert_eq!(found.variable(), None);
        assert_eq!(found.bound(), vec!["X"]);
        assert!(quantifier(&Term::apply("#Exists", vec![v("X"), v("Y"), v("Z")])).is_none());
        assert!(quantifier(&Term::apply("#Lambda", vec![v("X"), v("X")])).is_none());
    }

    #[test]
    fn a_quantifier_binds_its_variable_in_its_body_only() {
        let term = f(vec![v("X"), exists(v("X"), f(vec![v("X"), v("Y")]))]);
        assert_eq!(free_variables(&term), names(&["X", "Y"]));
        assert_eq!(bound_names(&term), vec!["X".to_owned()]);
        assert!(free_variables(&exists(v("X"), v("X"))).is_empty());
    }

    #[test]
    fn an_anonymous_variable_as_written_binds_nothing() {
        let term = exists(v("_"), f(vec![v("_"), v("X")]));
        assert_eq!(free_variables(&term), names(&["_", "X"]));
        assert!(bound_names(&term).is_empty());
        let resolved = exists(v("_Gen0"), f(vec![v("_Gen1"), v("_Gen0")]));
        assert_eq!(free_variables(&resolved), names(&["_Gen1"]));
    }

    #[test]
    fn a_malformed_binder_binds_each_of_its_names_once() {
        let term = exists(f(vec![v("X"), v("X")]), v("X"));
        let found = quantifier(&term).expect("a quantifier");
        assert_eq!(found.variable(), None);
        assert_eq!(found.bound(), vec!["X"]);
        assert_eq!(bound_names(&term), vec!["X".to_owned()]);
        let mut renamed = term.clone();
        let mut free = v("X");
        let renamings =
            rename_apart_in_sentence([&mut renamed, &mut free], &mut Reservation::new());
        assert_eq!(renamings, vec![("X".to_owned(), "X0".to_owned())]);
        assert_eq!(renamed, exists(f(vec![v("X0"), v("X0")]), v("X0")));
    }

    #[test]
    fn occurrences_give_each_variable_its_role_and_node() {
        let located = annotated(v("Y"), 7);
        let term = f(vec![
            v("X"),
            exists(v("X"), g(vec![v("X"), located.clone()])),
            exists(v("_"), v("_")),
        ]);
        let found = occurrences(&term);
        let roles: Vec<(&str, Role)> = found
            .iter()
            .map(|occurrence| (occurrence.name, occurrence.role))
            .collect();
        assert_eq!(
            roles,
            vec![
                ("X", Role::Free),
                ("X", Role::Binding { binder: 0 }),
                ("X", Role::Bound { binder: 0 }),
                ("Y", Role::Free),
                ("_", Role::Binding { binder: 1 }),
                ("_", Role::Free),
            ]
        );
        assert!(same_annotations(found[3].node, &located));
    }

    #[test]
    fn substitution_renames_a_binder_that_would_capture() {
        let mut term = exists(v("Y"), f(vec![v("X"), v("Y")]));
        let map = BTreeMap::from([("X".to_owned(), v("Y"))]);
        substitute(&mut term, &map, &mut Reservation::new());
        assert_eq!(term, exists(v("Y0"), f(vec![v("Y"), v("Y0")])));

        let mut term = exists(v("Y"), f(vec![v("X"), v("Y")]));
        let map = BTreeMap::from([("X".to_owned(), v("Z"))]);
        substitute(&mut term, &map, &mut Reservation::new());
        assert_eq!(term, exists(v("Y"), f(vec![v("Z"), v("Y")])));

        let mut term = f(vec![v("X"), exists(v("X"), v("X"))]);
        let map = BTreeMap::from([("X".to_owned(), Term::apply("c", Vec::new()))]);
        substitute(&mut term, &map, &mut Reservation::new());
        assert_eq!(
            term,
            f(vec![Term::apply("c", Vec::new()), exists(v("X"), v("X"))])
        );
    }

    /// The review's shapes: a rename of the binder must not take a key that the term does not
    /// hold, or that key replaces the occurrences just renamed.
    #[test]
    fn a_new_name_is_never_a_key_of_the_substitution() {
        let token = |text: &str| Term::Token {
            token: text.into(),
            sort: Sort::new("Int"),
        };
        let mut term = exists(v("X"), g(vec![v("Z"), v("X")]));
        let map = BTreeMap::from([
            ("Z".to_owned(), v("X")),
            ("X0".to_owned(), Term::apply("c", Vec::new())),
        ]);
        substitute(&mut term, &map, &mut Reservation::new());
        assert_eq!(term, exists(v("X1"), g(vec![v("X"), v("X1")])));

        let mut term = exists(v("K"), g(vec![v("X"), v("K")]));
        let map = BTreeMap::from([("X".to_owned(), v("K")), ("K0".to_owned(), token("5"))]);
        substitute(&mut term, &map, &mut Reservation::new());
        assert_eq!(term, exists(v("K1"), g(vec![v("K"), v("K1")])));
    }

    #[test]
    fn renaming_apart_keeps_the_first_binding_of_a_name_free_nowhere() {
        let mut body = Term::Rewrite {
            left: Box::new(v("X")),
            right: Box::new(v("X")),
        };
        let mut requires = exists(v("X"), f(vec![v("X")]));
        let mut ensures = f(vec![
            exists(v("Y"), f(vec![v("Y")])),
            exists(v("Y"), f(vec![v("Y"), v("X0")])),
        ]);
        let renamings = rename_apart_in_sentence(
            [&mut body, &mut requires, &mut ensures],
            &mut Reservation::new(),
        );
        assert_eq!(
            renamings,
            vec![
                ("X".to_owned(), "X1".to_owned()),
                ("Y".to_owned(), "Y0".to_owned())
            ]
        );
        assert_eq!(requires, exists(v("X1"), f(vec![v("X1")])));
        assert_eq!(
            ensures,
            f(vec![
                exists(v("Y"), f(vec![v("Y")])),
                exists(v("Y0"), f(vec![v("Y0"), v("X0")])),
            ])
        );
    }

    /// Mints of one stem continue from the last suffix tried, and never read as the names
    /// `resolve anonymous variables` gives.
    #[test]
    fn mints_count_per_stem_and_avoid_resolved_anonymous_spellings() {
        let mut reservation: Reservation = ["X1"].into_iter().collect();
        assert_eq!(reservation.mint("X"), "X0");
        assert_eq!(reservation.mint("X"), "X2");
        assert_eq!(reservation.mint("Y"), "Y0");
        assert_eq!(reservation.mint("_Gen"), "_Gen_0");
        assert_eq!(reservation.mint("?_Gen"), "?_Gen_0");
        assert_eq!(reservation.mint("_Gen3"), "_Gen3_0");
        assert_eq!(reservation.mint("_DotVar"), "_DotVar_0");
        assert_eq!(reservation.mint("_Genx"), "_Genx0");
        let mut binder = exists(v("_Gen3"), f(vec![v("_Gen3")]));
        let mut free = v("_Gen3");
        rename_apart_in_sentence([&mut binder, &mut free], &mut Reservation::new());
        assert_eq!(binder, exists(v("_Gen3_0"), f(vec![v("_Gen3_0")])));
    }

    /// Levels of the deep term below: more than a recursion of one frame per level takes on a
    /// test thread's stack.
    const DEEP: usize = 100_000;

    #[test]
    fn every_operation_takes_a_term_of_any_depth() {
        let mut chain = v("X");
        for _ in 0..DEEP {
            chain = f(vec![chain, v("Z")]);
        }
        let mut term = exists(v("Y"), f(vec![chain, v("Y")]));
        assert_eq!(free_variables(&term), names(&["X", "Z"]));
        assert_eq!(bound_names(&term), vec!["Y".to_owned()]);
        assert_eq!(occurrences(&term).len(), DEEP + 3);
        rename_bound(&mut term, &mut |_| Some("W".to_owned()));
        let map = BTreeMap::from([("X".to_owned(), v("W"))]);
        substitute(&mut term, &map, &mut Reservation::new());
        assert_eq!(free_variables(&term), names(&["W", "Z"]));
        assert_eq!(bound_names(&term), vec!["W0".to_owned()]);
        assert_eq!(
            rename_apart_in_sentence([&mut term, &mut v("W0")], &mut Reservation::new()),
            vec![("W0".to_owned(), "W00".to_owned())]
        );
    }
}
