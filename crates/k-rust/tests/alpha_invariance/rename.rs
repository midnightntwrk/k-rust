//! Alpha-renamings of the sentences of a loaded definition.
//!
//! Every renaming here maps a sentence to an alpha-variant of it under the binding rule of
//! `docs/testing.md`, "Alpha-invariance harness": after anonymous resolution each `_` is its own
//! variable, a quantifier `#Exists V . P` or `#Forall V . P` binds exactly `V` in `P`, and every
//! other variable of a rule, context, context alias or macro rule is bound by the sentence as a
//! whole; a claim binds its variables the same way. A renaming keeps each variable's sigil (`?`, `!`, `@`) and `_` prefix, and never renames
//! the fixed names `HOLE`, `HERE`, `#Configuration` (nor any other `#` or `$` name).
//!
//! A renaming is applied to the parsed sentence (the term the loader built), so the variant and
//! the original share every parsing decision and differ only in variable names.

use std::collections::{BTreeMap, BTreeSet};

use k_rust::{
    definition::{Attributes, Sentence},
    kast::{InternalLabel, Term},
};

/// One way of renaming a sentence's variables. Each yields an alpha-variant, or leaves the
/// sentence unchanged when it has nothing to rename.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Strategy {
    /// Every named variable to a fresh spelling, consistently across the sentence.
    Fresh,
    /// Every named variable to `K<i>`, in order of first occurrence: the spelling of the
    /// strictness and context variables the compiler mints.
    KIndex,
    /// Within each class (sigil and `_` prefix), each named variable to the spelling of the next
    /// one in order of first occurrence: every name becomes the name of another variable.
    Rotate,
    /// Every quantifier over a named variable to a fresh bound name, within its scope only.
    BinderApart,
    /// Every quantifier over a named variable to the spelling of another variable of the same
    /// class and the same inferred sort that occurs in the sentence but not in the quantifier's
    /// body, within its scope only: the binder then shadows that variable.
    BinderCapture,
    /// Every anonymous variable (`_`, `?_`, `!_`, `@_`) to its own fresh `_`-prefixed name.
    AnonNamed,
    /// As `BinderCapture`, whatever the sort of the shadowed variable: a binder over `Y:Bool`
    /// may take the name of the sentence's `X:Int`. A quantifier binds exactly its own variable,
    /// so the sort of a variable it shadows is irrelevant to the meaning.
    BinderCaptureAnySort,
    /// Every quantifier over a named variable to the name of a sibling binder: a quantifier of the
    /// same sentence in a disjoint scope (neither encloses the other) over a variable of the same
    /// class at another inferred sort, whose name does not occur in the renamed quantifier's
    /// body. The two binders then share one name at two sorts, each within its own scope.
    BinderCaptureSibling,
}

impl Strategy {
    pub const ALL: [Strategy; 8] = [
        Strategy::Fresh,
        Strategy::KIndex,
        Strategy::Rotate,
        Strategy::BinderApart,
        Strategy::BinderCapture,
        Strategy::AnonNamed,
        Strategy::BinderCaptureAnySort,
        Strategy::BinderCaptureSibling,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Strategy::Fresh => "fresh",
            Strategy::KIndex => "k-index",
            Strategy::Rotate => "rotate",
            Strategy::BinderApart => "binder-apart",
            Strategy::BinderCapture => "binder-capture",
            Strategy::AnonNamed => "anon-named",
            Strategy::BinderCaptureAnySort => "binder-capture-any-sort",
            Strategy::BinderCaptureSibling => "binder-capture-sibling",
        }
    }
}

/// The parts of a variable spelling a renaming keeps: its sigil and `_` prefix.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Spelling {
    sigil: &'static str,
    underscore: bool,
    stem: String,
}

impl Spelling {
    /// `None` for a fixed name, which no renaming touches.
    fn of(name: &str) -> Option<Spelling> {
        if matches!(name, "HOLE" | "HERE") || name.starts_with('#') || name.starts_with('$') {
            return None;
        }
        let (sigil, rest) = match name.chars().next() {
            Some('?') => ("?", &name[1..]),
            Some('!') => ("!", &name[1..]),
            Some('@') => ("@", &name[1..]),
            _ => ("", name),
        };
        let (underscore, stem) = match rest.strip_prefix('_') {
            Some(stem) => (true, stem),
            None => (false, rest),
        };
        Some(Spelling {
            sigil,
            underscore,
            stem: stem.to_owned(),
        })
    }

    fn anonymous(&self) -> bool {
        self.underscore && self.stem.is_empty()
    }

    fn class(&self) -> (&'static str, bool) {
        (self.sigil, self.underscore)
    }

    fn with_stem(&self, stem: &str) -> String {
        format!(
            "{}{}{stem}",
            self.sigil,
            if self.underscore { "_" } else { "" }
        )
    }
}

/// The attributes of a rule whose content names the rule's variables.
const VARIABLE_ATTRIBUTES: [&str; 3] = ["concrete", "symbolic", "unboundVariables"];

/// The variable a quantifier's first argument names: a variable, possibly under the semantic
/// cast that records its inferred sort at the loaded stage (`#SemanticCastToInt(X)`).
fn binder_variable(term: &Term) -> Option<(&str, Option<&str>)> {
    match term.unannotated() {
        Term::Variable { name, .. } => Some((name, None)),
        Term::Apply { label, arguments }
            if label.name.starts_with("#SemanticCastTo") && arguments.len() == 1 =>
        {
            match arguments[0].unannotated() {
                Term::Variable { name, .. } => Some((name, Some(label.name.as_str()))),
                _ => None,
            }
        }
        _ => None,
    }
}

fn is_quantifier(term: &Term) -> bool {
    matches!(term.unannotated(), Term::Apply { label, arguments }
        if (label.is(InternalLabel::Exists) || label.is(InternalLabel::Forall))
            && arguments.len() == 2
            && binder_variable(&arguments[0]).is_some())
}

/// A label that binds variables by a pattern (`#fun`, `#let`): a scope-local renaming does not
/// enter a quantifier whose body holds one, so its own binding needs no model here.
fn is_pattern_binder(term: &Term) -> bool {
    matches!(term.unannotated(), Term::Apply { label, .. }
        if label.is(InternalLabel::Fun2) || label.is(InternalLabel::Fun3) || label.is(InternalLabel::Let))
}

fn for_each_term<'a>(term: &'a Term, visit: &mut impl FnMut(&'a Term)) {
    visit(term);
    match term.unannotated() {
        Term::Rewrite { left, right } => {
            for_each_term(left, visit);
            for_each_term(right, visit);
        }
        Term::As { pattern, alias } => {
            for_each_term(pattern, visit);
            for_each_term(alias, visit);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                for_each_term(item, visit);
            }
        }
        _ => {}
    }
}

/// Every variable name of `term`, in order of first occurrence.
fn names_in(term: &Term, names: &mut Vec<String>) {
    for_each_term(term, &mut |term| {
        if let Term::Variable { name, .. } = term.unannotated()
            && !names.contains(name)
        {
            names.push(name.clone());
        }
    });
}

/// Rename every variable occurrence of `term` through `rename`, which sees each occurrence once.
fn map_variables(term: &mut Term, rename: &mut impl FnMut(&str) -> Option<String>) {
    match term {
        Term::Annotated { term, .. } => map_variables(term, rename),
        Term::Variable { name, .. } => {
            if let Some(new) = rename(name) {
                *name = new;
            }
        }
        Term::Rewrite { left, right } => {
            map_variables(left, rename);
            map_variables(right, rename);
        }
        Term::As { pattern, alias } => {
            map_variables(pattern, rename);
            map_variables(alias, rename);
        }
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => {
            for item in items {
                map_variables(item, rename);
            }
        }
        Term::InjectedLabel(_) | Term::Token { .. } => {}
    }
}

/// Rename the occurrences of `from` that a quantifier over `from` at the root of `term` binds:
/// the binder and the occurrences of its body not under an inner quantifier over `from`.
fn rename_bound(term: &mut Term, from: &str, to: &str) {
    fn body(term: &mut Term, from: &str, to: &str) {
        match term {
            Term::Annotated { term, .. } => body(term, from, to),
            Term::Variable { name, .. } => {
                if name == from {
                    *name = to.to_owned();
                }
            }
            Term::Apply { label, arguments }
                if (label.is(InternalLabel::Exists) || label.is(InternalLabel::Forall))
                    && is_quantifier_over(arguments, from) => {}
            Term::Rewrite { left, right } => {
                body(left, from, to);
                body(right, from, to);
            }
            Term::As { pattern, alias } => {
                body(pattern, from, to);
                body(alias, from, to);
            }
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            } => {
                for item in items {
                    body(item, from, to);
                }
            }
            Term::InjectedLabel(_) | Term::Token { .. } => {}
        }
    }
    fn is_quantifier_over(arguments: &[Term], from: &str) -> bool {
        arguments.len() == 2 && binder_variable(&arguments[0]).is_some_and(|(name, _)| name == from)
    }
    let mut node = term;
    while let Term::Annotated { term, .. } = node {
        node = term;
    }
    let Term::Apply { arguments, .. } = node else {
        unreachable!("rename_bound is called on a quantifier");
    };
    for argument in arguments.iter_mut() {
        body(argument, from, to);
    }
}

/// The parts of a sentence a renaming reads and writes: its terms and its attributes.
pub struct SentenceTerms<'a> {
    pub terms: Vec<&'a mut Term>,
    pub attributes: &'a mut Attributes,
}

/// The renamable parts of `sentence`, or `None` for a sentence whose variables no renaming
/// touches (syntax, configurations).
pub fn sentence_terms(sentence: &mut Sentence) -> Option<SentenceTerms<'_>> {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        } => Some(SentenceTerms {
            terms: vec![body, requires, ensures],
            attributes,
        }),
        Sentence::Context {
            body,
            requires,
            attributes,
        }
        | Sentence::ContextAlias {
            body,
            requires,
            attributes,
        } => Some(SentenceTerms {
            terms: vec![body, requires],
            attributes,
        }),
        _ => None,
    }
}

/// Every variable name of `sentence`'s renamable parts, in order of first occurrence.
pub fn variable_names(sentence: &Sentence) -> Vec<String> {
    let mut sentence = sentence.clone();
    let mut names = Vec::new();
    if let Some(parts) = sentence_terms(&mut sentence) {
        for term in &parts.terms {
            names_in(term, &mut names);
        }
    }
    names
}

/// Rename the names listed in the variable-naming attributes through `map`. Only the listed
/// names change: the separators and every name `map` keeps stay byte-identical, and an attribute
/// none of whose names changes is not rewritten.
fn rename_attributes(attributes: &mut Attributes, map: &BTreeMap<String, String>) {
    for key in VARIABLE_ATTRIBUTES {
        let Some(content) = attributes.get_str(key).map(str::to_owned) else {
            continue;
        };
        let mut renamed = String::with_capacity(content.len());
        let mut changed = false;
        for (index, item) in content.split(',').enumerate() {
            if index > 0 {
                renamed.push(',');
            }
            let name = item.trim();
            match map.get(name) {
                Some(new) if new != name && !name.is_empty() => {
                    let start = item.len() - item.trim_start().len();
                    renamed.push_str(&item[..start]);
                    renamed.push_str(new);
                    renamed.push_str(&item[start + name.len()..]);
                    changed = true;
                }
                _ => renamed.push_str(item),
            }
        }
        if changed {
            attributes.insert(key, serde_json::Value::String(renamed));
        }
    }
}

/// Apply `strategy` to `sentence`; true when it changed a name.
pub fn rename_sentence(sentence: &mut Sentence, strategy: Strategy) -> bool {
    let Some(parts) = sentence_terms(sentence) else {
        return false;
    };
    let SentenceTerms {
        mut terms,
        attributes,
    } = parts;
    let mut names = Vec::new();
    for term in &terms {
        names_in(term, &mut names);
    }
    let named: Vec<(String, Spelling)> = names
        .iter()
        .filter_map(|name| Spelling::of(name).map(|spelling| (name.clone(), spelling)))
        .filter(|(_, spelling)| !spelling.anonymous())
        .collect();
    match strategy {
        Strategy::Fresh | Strategy::KIndex | Strategy::Rotate => {
            let map = global_map(&named, strategy);
            if map.iter().all(|(from, to)| from == to) {
                return false;
            }
            for term in terms.iter_mut() {
                map_variables(term, &mut |name| map.get(name).cloned());
            }
            rename_attributes(attributes, &map);
            true
        }
        Strategy::AnonNamed => {
            let taken: BTreeSet<String> = names.iter().cloned().collect();
            let mut index = 0;
            // Each anonymous spelling (`_`, `?_`, ...) and the names its occurrences received.
            let mut minted = BTreeMap::<String, Vec<String>>::new();
            for term in terms.iter_mut() {
                map_variables(term, &mut |name| {
                    let spelling = Spelling::of(name)?;
                    if !spelling.anonymous() {
                        return None;
                    }
                    let new = loop {
                        let candidate = spelling.with_stem(&format!("Aq{index}"));
                        index += 1;
                        if !taken.contains(&candidate) {
                            break candidate;
                        }
                    };
                    minted.entry(name.to_owned()).or_default().push(new.clone());
                    Some(new)
                });
            }
            // An attribute that lists an anonymous spelling (`unboundVariables(_)`) names every
            // variable written with it, so it lists every name they received.
            let listed: BTreeMap<String, String> = minted
                .iter()
                .map(|(anonymous, names)| (anonymous.clone(), names.join(", ")))
                .collect();
            rename_attributes(attributes, &listed);
            !minted.is_empty()
        }
        Strategy::BinderApart
        | Strategy::BinderCapture
        | Strategy::BinderCaptureAnySort
        | Strategy::BinderCaptureSibling => {
            let mut index = 0;
            let mut changed = false;
            let taken: BTreeSet<String> = names.iter().cloned().collect();
            for position in 0..terms.len() {
                let mut quantifiers = Vec::new();
                quantifier_paths(&*terms[position], &mut Vec::new(), &mut quantifiers);
                for path in quantifiers {
                    // The sentence as it stands, so each later quantifier sees earlier renamings.
                    let mut outside = Vec::new();
                    for (other, term) in terms.iter().enumerate() {
                        if other == position {
                            names_outside(term, &path, &mut outside);
                        } else {
                            names_in(term, &mut outside);
                        }
                    }
                    let node = at_path_ref(&*terms[position], &path);
                    let Term::Apply { arguments, .. } = node.unannotated() else {
                        unreachable!()
                    };
                    let Some((bound, sort)) = binder_variable(&arguments[0]) else {
                        unreachable!()
                    };
                    let Some(spelling) = Spelling::of(bound) else {
                        continue;
                    };
                    if spelling.anonymous() {
                        continue;
                    }
                    let mut in_body = Vec::new();
                    names_in(&arguments[1], &mut in_body);
                    let mut holds_pattern_binder = false;
                    for_each_term(&arguments[1], &mut |term| {
                        holds_pattern_binder |= is_pattern_binder(term);
                    });
                    if holds_pattern_binder {
                        continue;
                    }
                    let bound = bound.to_owned();
                    let sort = sort.map(str::to_owned);
                    let target = match strategy {
                        Strategy::BinderApart => loop {
                            let candidate = spelling.with_stem(&format!("Bq{index}"));
                            index += 1;
                            if !taken.contains(&candidate) {
                                break Some(candidate);
                            }
                        },
                        Strategy::BinderCaptureSibling => {
                            let Some(sort) = &sort else {
                                continue;
                            };
                            sibling_binders(&terms, position, &path)
                                .into_iter()
                                .find(|(name, other_sort)| {
                                    *name != bound
                                        && !in_body.contains(name)
                                        && other_sort != sort
                                        && Spelling::of(name).is_some_and(|other| {
                                            !other.anonymous() && other.class() == spelling.class()
                                        })
                                })
                                .map(|(name, _)| name)
                        }
                        _ => outside
                            .iter()
                            .filter(|name| **name != bound && !in_body.contains(name))
                            .filter(|name| {
                                Spelling::of(name).is_some_and(|other| {
                                    !other.anonymous() && other.class() == spelling.class()
                                })
                            })
                            .find(|name| {
                                strategy == Strategy::BinderCaptureAnySort
                                    || sort.is_none()
                                    || sort_of(&terms, name) == sort
                            })
                            .cloned(),
                    };
                    if let Some(target) = target {
                        rename_bound(at_path(&mut *terms[position], &path), &bound, &target);
                        changed = true;
                    }
                }
            }
            changed
        }
    }
}

fn global_map(named: &[(String, Spelling)], strategy: Strategy) -> BTreeMap<String, String> {
    let mut map = BTreeMap::new();
    match strategy {
        Strategy::Fresh | Strategy::KIndex => {
            for (index, (name, spelling)) in named.iter().enumerate() {
                let stem = if strategy == Strategy::Fresh {
                    format!("Vq{index}")
                } else {
                    format!("K{index}")
                };
                map.insert(name.clone(), spelling.with_stem(&stem));
            }
        }
        _ => {
            let mut classes: BTreeMap<(&str, bool), Vec<&(String, Spelling)>> = BTreeMap::new();
            for entry in named {
                classes.entry(entry.1.class()).or_default().push(entry);
            }
            for members in classes.values() {
                for (index, (name, _)) in members.iter().enumerate() {
                    let next = &members[(index + 1) % members.len()].0;
                    map.insert(name.clone(), next.clone());
                }
            }
        }
    }
    map
}

/// The paths (argument indices from the root) of every quantifier of `term`, outermost first.
fn quantifier_paths(term: &Term, path: &mut Vec<usize>, found: &mut Vec<Vec<usize>>) {
    if is_quantifier(term) {
        found.push(path.clone());
    }
    let children: Vec<&Term> = match term.unannotated() {
        Term::Rewrite { left, right } => vec![left, right],
        Term::As { pattern, alias } => vec![pattern, alias],
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => items.iter().collect(),
        _ => Vec::new(),
    };
    for (index, child) in children.into_iter().enumerate() {
        path.push(index);
        quantifier_paths(child, path, found);
        path.pop();
    }
}

fn at_path_ref<'a>(term: &'a Term, path: &[usize]) -> &'a Term {
    let mut node = term;
    for &step in path {
        node = match node.unannotated() {
            Term::Rewrite { left, right } => {
                if step == 0 {
                    left
                } else {
                    right
                }
            }
            Term::As { pattern, alias } => {
                if step == 0 {
                    pattern
                } else {
                    alias
                }
            }
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            } => &items[step],
            _ => unreachable!("a quantifier path follows the term"),
        };
    }
    node
}

fn at_path<'a>(term: &'a mut Term, path: &[usize]) -> &'a mut Term {
    let mut node = term;
    for &step in path {
        while let Term::Annotated { term, .. } = node {
            node = term;
        }
        node = match node {
            Term::Rewrite { left, right } => {
                if step == 0 {
                    left
                } else {
                    right
                }
            }
            Term::As { pattern, alias } => {
                if step == 0 {
                    pattern
                } else {
                    alias
                }
            }
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            } => &mut items[step],
            _ => unreachable!("a quantifier path follows the term"),
        };
    }
    node
}

/// The variable names of `term` outside the subterm at `path`, in order of first occurrence.
fn names_outside(term: &Term, path: &[usize], names: &mut Vec<String>) {
    let Some((&step, rest)) = path.split_first() else {
        return;
    };
    let children: Vec<&Term> = match term.unannotated() {
        Term::Rewrite { left, right } => vec![left, right],
        Term::As { pattern, alias } => vec![pattern, alias],
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => items.iter().collect(),
        _ => Vec::new(),
    };
    for (index, child) in children.into_iter().enumerate() {
        if index == step {
            names_outside(child, rest, names);
        } else {
            names_in(child, names);
        }
    }
}

/// The bound name and the inferred sort (semantic cast) of every quantifier of `terms` whose scope
/// is disjoint from the quantifier at `path` of `terms[position]`: in another term, or in the same
/// term at a path neither a prefix nor an extension of `path`; in order of position, then
/// preorder.
fn sibling_binders(terms: &[&mut Term], position: usize, path: &[usize]) -> Vec<(String, String)> {
    let mut siblings = Vec::new();
    for (other, term) in terms.iter().enumerate() {
        let mut quantifiers = Vec::new();
        quantifier_paths(term, &mut Vec::new(), &mut quantifiers);
        for other_path in quantifiers {
            if other == position && (other_path.starts_with(path) || path.starts_with(&other_path))
            {
                continue;
            }
            let Term::Apply { arguments, .. } = at_path_ref(term, &other_path).unannotated() else {
                unreachable!()
            };
            if let Some((name, Some(sort))) = binder_variable(&arguments[0]) {
                siblings.push((name.to_owned(), sort.to_owned()));
            }
        }
    }
    siblings
}

/// Rename every quantifier of `sentence` over `from` to `to`, each within its own scope (the
/// binder and the occurrences of its body that it binds); true when one was renamed.
pub fn rename_binders(sentence: &mut Sentence, from: &str, to: &str) -> bool {
    let Some(parts) = sentence_terms(sentence) else {
        return false;
    };
    let mut changed = false;
    for term in parts.terms {
        let mut quantifiers = Vec::new();
        quantifier_paths(term, &mut Vec::new(), &mut quantifiers);
        for path in quantifiers {
            let Term::Apply { arguments, .. } = at_path_ref(term, &path).unannotated() else {
                unreachable!()
            };
            if binder_variable(&arguments[0]).is_some_and(|(name, _)| name == from) {
                rename_bound(at_path(term, &path), from, to);
                changed = true;
            }
        }
    }
    changed
}

/// Rename every occurrence of the variable `from` in `sentence` to `to`, whatever binds it; an
/// alpha-renaming when `to` occurs nowhere in the sentence and every occurrence of `from` is one
/// variable. True when one was renamed.
pub fn rename_variable(sentence: &mut Sentence, from: &str, to: &str) -> bool {
    fn walk(term: &mut Term, from: &str, to: &str, changed: &mut bool) {
        let mut node = &mut *term;
        while let Term::Annotated { term: inner, .. } = node {
            node = inner;
        }
        if let Term::Variable { name, .. } = node
            && name == from
        {
            *name = to.to_owned();
            *changed = true;
        }
        for child in term.children_mut() {
            walk(child, from, to, changed);
        }
    }
    let Some(parts) = sentence_terms(sentence) else {
        return false;
    };
    let mut changed = false;
    for term in parts.terms {
        walk(term, from, to, &mut changed);
    }
    changed
}

/// The text edits that turn the source of `original` into the source of `renamed`, a renaming of
/// it: for each variable occurrence whose name differs, the byte offset of the occurrence in the
/// parsed text and the two names. An occurrence without a source span is an error.
pub fn renamed_occurrences(
    original: &Sentence,
    renamed: &Sentence,
) -> Result<Vec<(usize, String, String)>, String> {
    fn walk(
        left: &Term,
        right: &Term,
        span: Option<usize>,
        edits: &mut Vec<(usize, String, String)>,
    ) -> Result<(), String> {
        match (left, right) {
            (
                Term::Annotated {
                    term: left,
                    metadata,
                },
                Term::Annotated { term: right, .. },
            ) => walk(
                left,
                right,
                metadata.span.as_ref().map(|span| span.start).or(span),
                edits,
            ),
            (Term::Variable { name: from, .. }, Term::Variable { name: to, .. }) => {
                if from != to {
                    let at = span.ok_or_else(|| format!("the occurrence of {from} has no span"))?;
                    edits.push((at, from.clone(), to.clone()));
                }
                Ok(())
            }
            (Term::Rewrite { left: a, right: b }, Term::Rewrite { left: c, right: d })
            | (
                Term::As {
                    pattern: a,
                    alias: b,
                },
                Term::As {
                    pattern: c,
                    alias: d,
                },
            ) => {
                walk(a, c, None, edits)?;
                walk(b, d, None, edits)
            }
            (Term::Sequence(left), Term::Sequence(right))
            | (
                Term::Apply {
                    arguments: left, ..
                },
                Term::Apply {
                    arguments: right, ..
                },
            ) => {
                for (left, right) in left.iter().zip(right) {
                    walk(left, right, None, edits)?;
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }
    let (mut original, mut renamed) = (original.clone(), renamed.clone());
    let (Some(left), Some(right)) = (sentence_terms(&mut original), sentence_terms(&mut renamed))
    else {
        return Ok(Vec::new());
    };
    let mut edits = Vec::new();
    for (left, right) in left.terms.iter().zip(&right.terms) {
        walk(left, right, None, &mut edits)?;
    }
    Ok(edits)
}

/// The semantic cast an occurrence of `name` carries in `terms` (its inferred sort), if any.
fn sort_of(terms: &[&mut Term], name: &str) -> Option<String> {
    let mut found = None;
    for term in terms {
        for_each_term(term, &mut |term| {
            if found.is_none()
                && let Some((other, Some(cast))) = binder_variable(term)
                && other == name
            {
                found = Some(cast.to_owned());
            }
        });
    }
    found
}
