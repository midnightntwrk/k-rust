//! The binding structure of K terms, with variables named by strings.
//!
//! This module states once which occurrences of a name a quantifier binds, and gives the
//! operations that a pass reading or rewriting variables under quantifiers needs: binder
//! recognition ([`quantifier`], [`quantifier_kind`]), the free and the bound names
//! ([`free_variables`], [`bound_names`]), the renaming of bound variables ([`rename_bound`]), the
//! renaming apart of a sentence's bound variables ([`rename_apart_in_sentence`]), and
//! capture-avoiding substitution ([`substitute`]).
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
//! substitution that respects binding.
//!
//! # Fresh names
//!
//! A bound variable that [`rename_apart_in_sentence`] or [`substitute`] renames takes the first
//! name `{name}{n}`, for `n` = 0, 1, 2, …, that is not reserved: so it keeps its sigil (`?`, `!`
//! or `@`) and its `_` prefix, which mean something of their own.
//! Every name of the terms involved is reserved, so a new name captures nothing and is captured
//! by nothing, and each new name is reserved in turn.
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

    /// The names this quantifier binds in its body: the variables of its binder in preorder,
    /// without the unresolved anonymous ones.
    pub fn bound(&self) -> Vec<&'t str> {
        let mut names = Vec::new();
        let mut pending = vec![self.binder];
        // Invariant: `names` holds the bound names of the binder's nodes visited so far, in
        // preorder, and `pending` the unvisited ones, the next on top; each pop visits one node.
        while let Some(node) = pending.pop() {
            if let Term::Variable { name, .. } = node.unannotated() {
                if !is_unresolved_anonymous(name) {
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

/// The names the quantifiers of `term` bind, one entry per bound variable of each quantifier, in
/// preorder; a name bound by two quantifiers occurs twice.
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

/// Rename bound variables in `term`: each quantifier, in preorder, asks `rename` for each name it
/// binds; where `rename` gives a new name, the binder's variable and every occurrence the
/// quantifier binds take it.
///
/// Free occurrences, and occurrences a nested quantifier binds again, keep their names.
/// The result is alpha-equivalent to `term` when no new name is free in the body of its
/// quantifier or bound by a quantifier inside it around an occurrence it renames; a new name
/// that occurs nowhere in `term` meets both.
pub fn rename_bound(term: &mut Term, rename: &mut impl FnMut(&str) -> Option<String>) {
    rename_in(term, &mut Vec::new(), rename);
}

/// Rename the bound variables of one sentence apart, given its term-bearing fields (as
/// `Sentence::terms_mut` lists them): afterwards no name is bound by two quantifiers, and no
/// bound name is free in any of the terms.
///
/// In preorder over the terms in order, a quantifier keeps a name that is free in none of the
/// terms and that no earlier quantifier binds, and renames every other to a fresh name (module
/// documentation, "Fresh names"). `reserved` holds names the new names must also avoid; on
/// return it holds every name of the terms and every new name as well.
/// Returns each renaming in the order made, the old name and the new one.
///
/// Each term stays alpha-equivalent to its input, and terms already apart are left unchanged.
pub fn rename_apart_in_sentence<'a>(
    terms: impl IntoIterator<Item = &'a mut Term>,
    reserved: &mut BTreeSet<String>,
) -> Vec<(String, String)> {
    let mut terms: Vec<&mut Term> = terms.into_iter().collect();
    let mut free = BTreeSet::new();
    for term in &terms {
        reserve_names(term, reserved);
        free.extend(free_variables(term));
    }
    let mut kept = BTreeSet::new();
    let mut renamed = Vec::new();
    for term in &mut terms {
        rename_bound(term, &mut |name| {
            if !free.contains(name) && kept.insert(name.to_owned()) {
                return None;
            }
            let new = fresh_name(name, reserved);
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
/// the replacement's variable is not captured; no other bound variable is renamed. `reserved` holds names the new names must also avoid; on
/// return it holds every name of `term` and of the replacements, and every new name.
/// A replacement takes the place of the whole occurrence, its annotations included.
/// A key that is an unresolved anonymous name names no single variable, so it replaces nothing.
///
/// The result is alpha-equivalent to the substitution of the replacements into `term` that
/// respects binding.
pub fn substitute(term: &mut Term, map: &BTreeMap<String, Term>, reserved: &mut BTreeSet<String>) {
    reserve_names(term, reserved);
    for replacement in map.values() {
        reserve_names(replacement, reserved);
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
            for_each_bound_variable(binder, &mut |name| {
                let new = rename(name);
                scope.push((name.clone(), new.clone()));
                if let Some(new) = new {
                    *name = new;
                }
            });
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
    reserved: &mut BTreeSet<String>,
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
            let mut names = Vec::new();
            for_each_bound_variable(binder, &mut |name| names.push(name.clone()));
            let mut inner = active.clone();
            for name in &names {
                inner.remove(name.as_str());
            }
            if inner.is_empty() {
                return;
            }
            let captures = |name: &str, body_free: &BTreeSet<String>| {
                inner
                    .keys()
                    .any(|key| body_free.contains(*key) && free_in[key].contains(name))
            };
            if names
                .iter()
                .any(|name| inner.keys().any(|key| free_in[key].contains(name)))
            {
                let body_free = free_variables(body);
                let mut renames = BTreeMap::new();
                for name in names {
                    if !renames.contains_key(&name) && captures(&name, &body_free) {
                        let new = fresh_name(&name, reserved);
                        renames.insert(name, new);
                    }
                }
                if !renames.is_empty() {
                    for_each_bound_variable(binder, &mut |name| {
                        if let Some(new) = renames.get(name.as_str()) {
                            name.clone_from(new);
                        }
                    });
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

/// Add the name of every variable of `term`, binders included, to `reserved`.
fn reserve_names(term: &Term, reserved: &mut BTreeSet<String>) {
    term.visit_preorder(&mut |node| {
        if let Term::Variable { name, .. } = node {
            reserved.insert(name.clone());
        }
    });
}

/// The first name `{stem}{n}`, for `n` = 0, 1, …, outside `reserved`, which it is added to.
fn fresh_name(stem: &str, reserved: &mut BTreeSet<String>) -> String {
    let mut suffix = 0_usize;
    // Invariant: every name `{stem}{m}` with `m < suffix` is reserved; `reserved` is finite, so
    // an unreserved name is found within `reserved.len() + 1` tries.
    loop {
        let candidate = format!("{stem}{suffix}");
        if !reserved.contains(&candidate) {
            reserved.insert(candidate.clone());
            return candidate;
        }
        suffix += 1;
    }
}

#[cfg(test)]
mod tests {
    //! The operations are checked against a locally nameless reference ([`Nameless`]): a bound
    //! occurrence is the number of quantifiers between it and its binder, so alpha-equivalent
    //! terms have equal forms, and substitution for a free name renames nothing. The oracle
    //! recognises binders by its own reading of the rule and shares no code with the module.

    use std::collections::{BTreeMap, BTreeSet};

    use proptest::prelude::*;

    use super::{
        QuantifierKind, bound_names, free_variables, quantifier, rename_apart_in_sentence,
        rename_bound, substitute,
    };
    use crate::kast::{Label, Sort, Term, TermMetadata};

    // ------------------------------------------------------------------ the reference oracle

    /// A term in locally nameless form.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Nameless {
        Free {
            name: String,
            sort: Option<Sort>,
        },
        /// `index` quantifiers lie between the occurrence and its binder.
        Bound {
            index: usize,
            sort: Option<Sort>,
        },
        Quantifier {
            label: Label,
            binder: Binder,
            body: Box<Nameless>,
        },
        Node {
            head: Head,
            children: Vec<Nameless>,
        },
    }

    /// A quantifier's binder without the bound name.
    #[derive(Clone, Debug, Eq, PartialEq)]
    enum Binder {
        /// A variable under `casts`, outermost first: its sort, its sigil and `_` prefix, and
        /// whether it is an anonymous variable as written, which binds nothing.
        Variable {
            casts: Vec<Label>,
            sort: Option<Sort>,
            sigil: Option<char>,
            underscore: bool,
            anonymous: bool,
        },
        /// A binder holding no variable, which binds nothing.
        Other(Box<Nameless>),
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

    /// The binder without its name, and the name it binds.
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "the generated binders are variables, casts of variables, or variable-free"
    )]
    fn oracle_binder(binder: &Term) -> (Binder, Option<String>) {
        let mut casts = Vec::new();
        let mut node = binder.unannotated();
        // Invariant: `casts` are the casts above `node`, outermost first.
        while let Term::Apply { label, arguments } = node
            && label.name.starts_with("#SemanticCastTo")
            && arguments.len() == 1
        {
            casts.push(label.clone());
            node = arguments[0].unannotated();
        }
        match node {
            Term::Variable { name, sort } => {
                let anonymous = written_anonymous(name);
                let sigil = name.chars().next().filter(|first| "?!@".contains(*first));
                let rest = &name[sigil.map_or(0, char::len_utf8)..];
                (
                    Binder::Variable {
                        casts,
                        sort: sort.clone(),
                        sigil,
                        underscore: rest.starts_with('_'),
                        anonymous,
                    },
                    (!anonymous).then(|| name.clone()),
                )
            }
            _ => {
                assert!(casts.is_empty(), "a generated cast holds a variable");
                (
                    Binder::Other(Box::new(nameless(binder, &mut Vec::new()))),
                    None,
                )
            }
        }
    }

    /// `term` in locally nameless form, under the binders `scope` (innermost last; `None` for one
    /// that binds nothing).
    fn nameless(term: &Term, scope: &mut Vec<Option<String>>) -> Nameless {
        if let Some((label, binder, body)) = oracle_quantifier(term) {
            let (binder, bound) = oracle_binder(binder);
            scope.push(bound);
            let body = nameless(body, scope);
            scope.pop();
            return Nameless::Quantifier {
                label: label.clone(),
                binder,
                body: Box::new(body),
            };
        }
        let node = |head, children: Vec<&Term>, scope: &mut Vec<Option<String>>| Nameless::Node {
            head,
            children: children
                .into_iter()
                .map(|child| nameless(child, scope))
                .collect(),
        };
        match term.unannotated() {
            Term::Variable { name, sort } => {
                match scope
                    .iter()
                    .rev()
                    .position(|bound| bound.as_deref() == Some(name.as_str()))
                {
                    Some(index) => Nameless::Bound {
                        index,
                        sort: sort.clone(),
                    },
                    None => Nameless::Free {
                        name: name.clone(),
                        sort: sort.clone(),
                    },
                }
            }
            Term::InjectedLabel(label) => node(Head::InjectedLabel(label.clone()), vec![], scope),
            Term::Rewrite { left, right } => node(Head::Rewrite, vec![left, right], scope),
            Term::As { pattern, alias } => node(Head::As, vec![pattern, alias], scope),
            Term::Sequence(items) => node(Head::Sequence, items.iter().collect(), scope),
            Term::Apply { label, arguments } => node(
                Head::Apply(label.clone()),
                arguments.iter().collect(),
                scope,
            ),
            Term::Token { token, sort } => {
                node(Head::Token(token.clone(), sort.clone()), vec![], scope)
            }
            Term::Annotated { .. } => unreachable!("unannotated strips annotations"),
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
            Nameless::Bound { .. } => {}
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
            names.extend(oracle_binder(binder).1);
            oracle_bound(body, names);
        } else {
            for child in term.children() {
                oracle_bound(child, names);
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
            Nameless::Free { .. } | Nameless::Bound { .. } => form.clone(),
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

    /// Substitution that respects binding but renames nothing: right exactly when no binder
    /// would capture a replacement's variable.
    fn substitute_without_renaming(term: &Term, map: &BTreeMap<String, Term>) -> Term {
        if let Some((label, binder, body)) = oracle_quantifier(term) {
            let mut inner = map.clone();
            if let Some(name) = oracle_binder(binder).1 {
                inner.remove(&name);
            }
            return Term::Apply {
                label: label.clone(),
                arguments: vec![binder.clone(), substitute_without_renaming(body, &inner)],
            };
        }
        let mut copy = term.clone();
        if let Term::Variable { name, .. } = term.unannotated()
            && !written_anonymous(name)
            && let Some(replacement) = map.get(name)
        {
            return replacement.clone();
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

    // ------------------------------------------------------------------ generators

    /// Names that collide with the fresh names (`X0`, `Y0`) and carry each spelling class.
    const NAMES: [&str; 9] = ["X", "Y", "Z", "X0", "Y0", "?X", "_A", "_", "?_"];

    fn name() -> impl Strategy<Value = String> {
        prop::sample::select(&NAMES[..]).prop_map(str::to_owned)
    }

    fn sort() -> impl Strategy<Value = Option<Sort>> {
        prop_oneof![
            Just(None),
            Just(Some(Sort::new("Int"))),
            Just(Some(Sort::new("Bool"))),
        ]
    }

    fn annotated(term: Term) -> Term {
        term.with_metadata(TermMetadata {
            sort: Some(Sort::new("K")),
            ..TermMetadata::default()
        })
    }

    fn variable() -> impl Strategy<Value = Term> {
        (name(), sort()).prop_map(|(name, sort)| Term::Variable { name, sort })
    }

    /// A binder: a variable, annotated or not, under a semantic cast or not; or a token.
    fn binder() -> impl Strategy<Value = Term> {
        prop_oneof![
            4 => variable(),
            1 => variable().prop_map(annotated),
            1 => variable().prop_map(|variable| Term::apply("#SemanticCastToInt", vec![variable])),
            1 => Just(Term::Token {
                token: "1".into(),
                sort: Sort::new("Int"),
            }),
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

    /// Terms of up to four levels over every constructor, mostly quantifiers of both kinds and
    /// applications, with annotations, and `#Exists` applied to a number of arguments other than
    /// two.
    fn term() -> BoxedStrategy<Term> {
        term_of_depth(4)
    }

    fn term_of_depth(depth: u32) -> BoxedStrategy<Term> {
        let leaf = prop_oneof![
            6 => variable(),
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
            5 => (any::<bool>(), binder(), inner.clone()).prop_map(|(exists, binder, body)| {
                let kind = if exists { QuantifierKind::Exists } else { QuantifierKind::Forall };
                quantified(kind, binder, body)
            }),
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
            1 => inner.clone().prop_map(annotated),
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
        let shadowing = (
            any::<bool>(),
            prop::sample::select(&NAMES[..7]).prop_map(str::to_owned),
            term_of_depth(2),
            term_of_depth(2),
        )
            .prop_map(|(exists, binder, beside, body)| {
                let kind = if exists {
                    QuantifierKind::Exists
                } else {
                    QuantifierKind::Forall
                };
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
            });
        prop_oneof![term(), shadowing]
    }

    /// A term and a substitution: either both drawn independently, or a term with a quantifier
    /// over `B` around a free `K`, and a substitution that replaces `K` by a term in which `B`
    /// is free, so the quantifier must rename `B`.
    fn substitution_case() -> impl Strategy<Value = (Term, BTreeMap<String, Term>)> {
        let named = || prop::sample::select(&NAMES[..7]).prop_map(str::to_owned);
        let capturing = (
            any::<bool>(),
            named(),
            named(),
            term_of_depth(2),
            term_of_depth(2),
            term_of_depth(1),
            substitution(),
        )
            .prop_filter("the key differs from the binder", |case| case.1 != case.2)
            .prop_map(|(exists, binder, key, beside, body, rest, mut map)| {
                let kind = if exists {
                    QuantifierKind::Exists
                } else {
                    QuantifierKind::Forall
                };
                let body = Term::apply("f", vec![Term::variable(key.clone()), body]);
                let term = Term::apply(
                    "g",
                    vec![
                        beside,
                        quantified(kind, Term::variable(binder.clone()), body),
                    ],
                );
                map.insert(key, Term::apply("f", vec![Term::variable(binder), rest]));
                (term, map)
            });
        prop_oneof![(term(), substitution()), capturing]
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
        #![proptest_config(ProptestConfig::with_cases(256))]

        /// The free names are the oracle's, and C1's before the port.
        #[test]
        fn free_variables_are_the_free_names_of_the_nameless_form(term in term()) {
            let mut expected = BTreeSet::new();
            oracle_free(&closed(&term), &mut expected);
            prop_assert_eq!(free_variables(&term), expected);
            prop_assert_eq!(free_variables(&term), c1_free_variables(&term));
        }

        /// `bound_names` lists each bound variable of each quantifier, in preorder.
        #[test]
        fn bound_names_list_every_binding_in_preorder(term in term()) {
            let mut expected = Vec::new();
            oracle_bound(&term, &mut expected);
            prop_assert_eq!(bound_names(&term), expected);
        }

        /// Renaming any choice of bound variables to unused names keeps the term alpha-equivalent,
        /// renames exactly the chosen bindings, keeps the free names, and is undone by the inverse
        /// renaming.
        #[test]
        fn renaming_bound_variables_to_unused_names_is_an_alpha_conversion(
            term in term_with_shadowing(),
            choices in prop::collection::vec(any::<bool>(), 0..8),
        ) {
            let (renamed, made) = renamed_to_fresh(&term, &choices);
            prop_assert_eq!(closed(&renamed), closed(&term));
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

        /// Renaming a sentence apart keeps each term alpha-equivalent, leaves the terms apart,
        /// renames nothing in terms already apart, and reserves every name it meets or makes.
        #[test]
        fn renaming_a_sentence_apart_keeps_its_meaning_and_makes_it_apart(
            terms in prop::collection::vec(term(), 1..4),
        ) {
            let mut renamed = terms.clone();
            let mut reserved = BTreeSet::from(["W".to_owned()]);
            let renamings = rename_apart_in_sentence(renamed.iter_mut(), &mut reserved);
            for (before, after) in terms.iter().zip(&renamed) {
                prop_assert_eq!(closed(after), closed(before));
                prop_assert!(names_of(before).is_subset(&reserved));
                prop_assert!(names_of(after).is_subset(&reserved));
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
            prop_assert!(rename_apart_in_sentence(renamed.iter_mut(), &mut BTreeSet::new()).is_empty());
            prop_assert_eq!(renamed, again);
        }

        /// Substitution agrees with substitution in locally nameless form, mints only names it
        /// reserves and that were not reserved before, and renames no binder where none would
        /// capture.
        #[test]
        fn substitution_is_the_nameless_substitution((term, map) in substitution_case()) {
            let mut result = term.clone();
            let before = BTreeSet::from(["W".to_owned()]);
            let mut reserved = before.clone();
            substitute(&mut result, &map, &mut reserved);
            let forms: BTreeMap<String, Nameless> =
                map.iter().map(|(name, replacement)| (name.clone(), closed(replacement))).collect();
            prop_assert_eq!(closed(&result), oracle_substitute(&closed(&term), &forms));
            let mut met = names_of(&term);
            for replacement in map.values() {
                met.extend(names_of(replacement));
            }
            prop_assert!(met.is_subset(&reserved));
            for name in names_of(&result).difference(&met) {
                prop_assert!(reserved.contains(name) && !before.contains(name));
            }
            let replacement_free: BTreeSet<String> = map.values().flat_map(free_variables).collect();
            if bound_names(&term).iter().all(|name| !replacement_free.contains(name)) {
                prop_assert_eq!(result, substitute_without_renaming(&term, &map));
            }
        }
    }

    /// The generators reach the cases the properties are about: a substitution that renames a
    /// binder to avoid capture, a sentence renamed apart, and a quantifier that rebinds a name
    /// bound around it.
    #[test]
    fn the_generators_reach_capture_and_shadowing() {
        use proptest::{
            strategy::ValueTree,
            test_runner::{Config, RngAlgorithm, TestRng, TestRunner},
        };

        let mut runner = TestRunner::new_with_rng(
            Config::default(),
            TestRng::deterministic_rng(RngAlgorithm::ChaCha),
        );
        let (mut captures, mut apart_renamings, mut shadowing) = (0, 0, 0);
        for _ in 0..256 {
            let (term, map) = substitution_case()
                .new_tree(&mut runner)
                .expect("a case")
                .current();
            let mut result = term.clone();
            substitute(&mut result, &map, &mut BTreeSet::new());
            if result != substitute_without_renaming(&term, &map) {
                captures += 1;
            }
            let mut renamed = term.clone();
            if !rename_apart_in_sentence([&mut renamed], &mut BTreeSet::new()).is_empty() {
                apart_renamings += 1;
            }
            let shadowed = term_with_shadowing()
                .new_tree(&mut runner)
                .expect("a term")
                .current();
            let bound = bound_names(&shadowed);
            if bound.iter().collect::<BTreeSet<_>>().len() < bound.len() {
                shadowing += 1;
            }
        }
        assert!(
            captures >= 64 && apart_renamings >= 24 && shadowing >= 64,
            "{captures} captures, {apart_renamings} sentences renamed apart, {shadowing} names bound twice"
        );
    }

    // ------------------------------------------------------------------ examples

    fn v(name: &str) -> Term {
        Term::variable(name)
    }

    fn f(arguments: Vec<Term>) -> Term {
        Term::apply("f", arguments)
    }

    fn exists(binder: Term, body: Term) -> Term {
        quantified(QuantifierKind::Exists, binder, body)
    }

    fn names(list: &[&str]) -> BTreeSet<String> {
        list.iter().map(|name| (*name).to_owned()).collect()
    }

    #[test]
    fn a_quantifier_is_exists_or_forall_of_two_arguments() {
        let term = annotated(exists(v("X"), f(vec![v("X")])));
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
    fn substitution_renames_a_binder_that_would_capture() {
        let mut term = exists(v("Y"), f(vec![v("X"), v("Y")]));
        let map = BTreeMap::from([("X".to_owned(), v("Y"))]);
        substitute(&mut term, &map, &mut BTreeSet::new());
        assert_eq!(term, exists(v("Y0"), f(vec![v("Y"), v("Y0")])));

        let mut term = exists(v("Y"), f(vec![v("X"), v("Y")]));
        let map = BTreeMap::from([("X".to_owned(), v("Z"))]);
        substitute(&mut term, &map, &mut BTreeSet::new());
        assert_eq!(term, exists(v("Y"), f(vec![v("Z"), v("Y")])));

        let mut term = f(vec![v("X"), exists(v("X"), v("X"))]);
        let map = BTreeMap::from([("X".to_owned(), Term::apply("c", Vec::new()))]);
        substitute(&mut term, &map, &mut BTreeSet::new());
        assert_eq!(
            term,
            f(vec![Term::apply("c", Vec::new()), exists(v("X"), v("X"))])
        );
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
            &mut BTreeSet::new(),
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
        rename_bound(&mut term, &mut |_| Some("W".to_owned()));
        let map = BTreeMap::from([("X".to_owned(), v("W"))]);
        substitute(&mut term, &map, &mut BTreeSet::new());
        assert_eq!(free_variables(&term), names(&["W", "Z"]));
        assert_eq!(bound_names(&term), vec!["W0".to_owned()]);
        assert_eq!(
            rename_apart_in_sentence([&mut term, &mut v("W0")], &mut BTreeSet::new()),
            vec![("W0".to_owned(), "W00".to_owned())]
        );
    }
}
