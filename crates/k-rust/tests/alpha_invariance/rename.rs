//! Alpha-renamings of the sentences of a loaded definition.
//!
//! Every renaming here maps a sentence to an alpha-variant of it under the binding rule of
//! `docs/testing.md`, "Alpha-invariance harness": after anonymous resolution each `_` is its own
//! variable, a quantifier `#Exists V . P` or `#Forall V . P` binds exactly `V` in `P`, and every
//! other variable of a rule, context, context alias or macro rule is bound by the sentence as a
//! whole. A renaming keeps each variable's sigil (`?`, `!`, `@`) and `_` prefix, and never renames
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
    /// class that occurs in the sentence but not in the quantifier's body, within its scope only:
    /// the binder then shadows that variable.
    BinderCapture,
    /// Every anonymous variable (`_`, `?_`, `!_`, `@_`) to its own fresh `_`-prefixed name.
    AnonNamed,
}

impl Strategy {
    pub const ALL: [Strategy; 6] = [
        Strategy::Fresh,
        Strategy::KIndex,
        Strategy::Rotate,
        Strategy::BinderApart,
        Strategy::BinderCapture,
        Strategy::AnonNamed,
    ];

    pub fn name(self) -> &'static str {
        match self {
            Strategy::Fresh => "fresh",
            Strategy::KIndex => "k-index",
            Strategy::Rotate => "rotate",
            Strategy::BinderApart => "binder-apart",
            Strategy::BinderCapture => "binder-capture",
            Strategy::AnonNamed => "anon-named",
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
/// touches (syntax, claims, configurations).
pub fn sentence_terms(sentence: &mut Sentence) -> Option<SentenceTerms<'_>> {
    match sentence {
        Sentence::Rule {
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

fn rename_attributes(attributes: &mut Attributes, map: &BTreeMap<String, String>) {
    for key in VARIABLE_ATTRIBUTES {
        let Some(content) = attributes.get_str(key) else {
            continue;
        };
        if content.trim().is_empty() {
            continue;
        }
        let renamed = content
            .split(',')
            .map(|name| {
                let name = name.trim();
                map.get(name).cloned().unwrap_or_else(|| name.to_owned())
            })
            .collect::<Vec<_>>()
            .join(", ");
        attributes.insert(key, serde_json::Value::String(renamed));
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
        Strategy::BinderApart | Strategy::BinderCapture => {
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
                        _ => outside
                            .iter()
                            .filter(|name| **name != bound && !in_body.contains(name))
                            .filter(|name| {
                                Spelling::of(name).is_some_and(|other| {
                                    !other.anonymous() && other.class() == spelling.class()
                                })
                            })
                            .find(|name| sort.is_none() || sort_of(&terms, name) == sort)
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
