//! Scoped binders for sort inference.
//!
//! A quantifier `#Exists X . P` or `#Forall X . P` binds the variables of its binder in its body
//! and nowhere else (`kast::binding`), so the variable it binds is a variable of its own, apart
//! from every other variable of the rule that has its spelling: the left side's `X`, a sibling
//! binder's `X`, an enclosing binder's `X`. Its sort is therefore inferred within its scope
//! only, and a rule infers exactly as the rule with that binder renamed apart does.
//!
//! The inference engines identify a variable by its name across a parse forest. So before
//! inference, [`Grammar::scope_binders`] renames each binder whose spelling stands for more than
//! one variable of the forest, with every occurrence it binds, to a spelling no source can write:
//! its name, [`MARK`] and a number. The forest is then an alpha-variant of the parse, which every
//! engine infers as a whole. After inference, [`restore_term`] gives each variable its written
//! name back, and [`restore_error`] does so in the texts of a rejection. A forest whose binders
//! are already apart is not changed, so neither is its inference.
//!
//! A binder is identified by the span of its variable, which is the same in every tree of the
//! forest, so the trees of an ambiguous parse agree on which variable each occurrence is.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::kast::binding::{is_unresolved_anonymous, quantifier_kind};
use crate::kast::{Term, TermSpan};

use super::forest::{PackedNode, PackedTerm};
use super::{AmbiguityPlace, AmbiguousParse, Grammar, ParseError};

/// The character that separates a binder's written name from the number that sets it apart. It
/// is a private-use code point, which no K variable token contains.
const MARK: char = '\u{E000}';

/// Which binder an occurrence belongs to: the span of the binder's variable, or the identity of
/// the variable's node when it has no span.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Binder {
    Span(TermSpan),
    Node(*const PackedTerm),
}

/// The names the quantifiers around a node bind there, each with its binder, innermost last.
type Scope = Vec<(String, Binder)>;

/// The variable leaves of `binder`, every alternative included, each with its name and the binder
/// it is.
fn binder_variables(binder: &Rc<PackedTerm>) -> Vec<(String, Binder)> {
    let mut found = Vec::new();
    let mut visited = HashSet::new();
    let mut pending = vec![Rc::clone(binder)];
    // Invariant: `visited` holds the nodes already scanned and `pending` reachable nodes not yet
    // scanned; each node is scanned once.
    while let Some(node) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&node)) {
            continue;
        }
        match &node.node {
            PackedNode::Term(leaf) => {
                if let Term::Variable { name, .. } = leaf.unannotated()
                    && !is_unresolved_anonymous(name)
                    && !found
                        .iter()
                        .any(|(found, _): &(String, Binder)| found == name)
                {
                    let binder = leaf
                        .metadata()
                        .and_then(|metadata| metadata.span)
                        .map_or(Binder::Node(Rc::as_ptr(&node)), Binder::Span);
                    found.push((name.clone(), binder));
                }
            }
            PackedNode::Production { children, .. }
            | PackedNode::InstantiatedProduction { children, .. } => {
                pending.extend(children.iter().rev().cloned());
            }
            PackedNode::Ambiguity(alternatives) => pending.extend(alternatives.iter().cloned()),
        }
    }
    found
}

/// The variable a name stands for at one occurrence: free, or the binder's.
type Identity = Option<Binder>;

impl Grammar {
    /// Whether `production` builds a quantifier node: a production of `#Exists` or `#Forall` over
    /// a binder and a body.
    fn is_quantifier_production(&self, production: usize) -> bool {
        let production = &self.productions[production];
        let node = production
            .term_production
            .map_or(production, |node| &self.productions[node]);
        production.nonterminals == 2
            && [production, node].iter().any(|production| {
                production
                    .label
                    .as_ref()
                    .is_some_and(|label| quantifier_kind(label).is_some())
            })
    }

    /// The binder and the body of `node` when it is a quantifier node.
    fn quantifier_parts<'a>(
        &self,
        node: &'a PackedTerm,
    ) -> Option<(&'a Rc<PackedTerm>, &'a Rc<PackedTerm>)> {
        match &node.node {
            PackedNode::Production {
                production,
                children,
                ..
            }
            | PackedNode::InstantiatedProduction {
                production,
                children,
                ..
            } if self.is_quantifier_production(*production) => match children.as_slice() {
                [binder, body] => Some((binder, body)),
                _ => None,
            },
            PackedNode::Production { .. }
            | PackedNode::InstantiatedProduction { .. }
            | PackedNode::Term(_)
            | PackedNode::Ambiguity(_) => None,
        }
    }

    /// `forest` with every binder that shares its spelling with another variable of the forest
    /// renamed apart, with the occurrences it binds (module docs); `None` when every binder is
    /// apart already, the forest of every rule without quantifiers among them.
    pub(super) fn scope_binders(&self, forest: &Rc<PackedTerm>) -> Option<Rc<PackedTerm>> {
        let mut identities: BTreeMap<String, BTreeSet<Identity>> = BTreeMap::new();
        self.collect_identities(
            forest,
            &mut Scope::new(),
            &mut HashSet::new(),
            &mut identities,
        );
        let mut renamed: HashMap<(String, Binder), String> = HashMap::new();
        for (name, identities) in &identities {
            if identities.len() < 2 {
                continue;
            }
            for (number, binder) in identities.iter().flatten().enumerate() {
                renamed.insert((name.clone(), *binder), format!("{name}{MARK}{number}"));
            }
        }
        if renamed.is_empty() {
            return None;
        }
        Some(self.rename_binders(forest, &mut Scope::new(), &renamed, &mut HashMap::new()))
    }

    /// Add to `identities`, for each variable name of `node` in `scope`, the variables it stands
    /// for there.
    fn collect_identities(
        &self,
        node: &Rc<PackedTerm>,
        scope: &mut Scope,
        visited: &mut HashSet<(*const PackedTerm, Scope)>,
        identities: &mut BTreeMap<String, BTreeSet<Identity>>,
    ) {
        if !visited.insert((Rc::as_ptr(node), scope.clone())) {
            return;
        }
        crate::stack::guarded(|| {
            if let Some((binder, body)) = self.quantifier_parts(node) {
                let depth = scope.len();
                for (name, key) in binder_variables(binder) {
                    identities
                        .entry(name.clone())
                        .or_default()
                        .insert(Some(key));
                    scope.push((name, key));
                }
                self.collect_identities(body, scope, visited, identities);
                scope.truncate(depth);
                return;
            }
            match &node.node {
                PackedNode::Term(leaf) => {
                    if let Term::Variable { name, .. } = leaf.unannotated()
                        && !is_unresolved_anonymous(name)
                    {
                        let identity = scope
                            .iter()
                            .rev()
                            .find(|(bound, _)| bound == name)
                            .map(|(_, binder)| *binder);
                        identities.entry(name.clone()).or_default().insert(identity);
                    }
                }
                PackedNode::Production { children, .. }
                | PackedNode::InstantiatedProduction { children, .. } => {
                    for child in children {
                        self.collect_identities(child, scope, visited, identities);
                    }
                }
                PackedNode::Ambiguity(alternatives) => {
                    for alternative in alternatives {
                        self.collect_identities(alternative, scope, visited, identities);
                    }
                }
            }
        });
    }

    /// `node` in `scope` with each occurrence of a binder `renamed` holds renamed; the node
    /// itself, shared, where nothing below it changes.
    fn rename_binders(
        &self,
        node: &Rc<PackedTerm>,
        scope: &mut Scope,
        renamed: &HashMap<(String, Binder), String>,
        memo: &mut HashMap<(*const PackedTerm, Scope), Rc<PackedTerm>>,
    ) -> Rc<PackedTerm> {
        let key = (Rc::as_ptr(node), scope.clone());
        if let Some(done) = memo.get(&key) {
            return Rc::clone(done);
        }
        let result = crate::stack::guarded(|| {
            if let Some((binder, body)) = self.quantifier_parts(node) {
                let depth = scope.len();
                for (name, key) in binder_variables(binder) {
                    if renamed.contains_key(&(name.clone(), key)) {
                        scope.push((name, key));
                    }
                }
                // The binder's own variables are in the scope of its new names.
                let children = [
                    self.rename_binders(binder, scope, renamed, memo),
                    self.rename_binders(body, scope, renamed, memo),
                ];
                scope.truncate(depth);
                return rebuilt(node, children.into());
            }
            match &node.node {
                PackedNode::Term(leaf) => {
                    let new = match leaf.unannotated() {
                        Term::Variable { name, .. } => scope
                            .iter()
                            .rev()
                            .find(|(bound, _)| bound == name)
                            .and_then(|(name, binder)| renamed.get(&(name.clone(), *binder))),
                        _ => None,
                    };
                    match new {
                        Some(new) => {
                            let mut leaf = leaf.clone();
                            if let Some(name) = variable_name_mut(&mut leaf) {
                                name.clone_from(new);
                            }
                            PackedTerm::leaf(leaf)
                        }
                        None => Rc::clone(node),
                    }
                }
                PackedNode::Production { children, .. }
                | PackedNode::InstantiatedProduction { children, .. } => {
                    let children = children
                        .iter()
                        .map(|child| self.rename_binders(child, scope, renamed, memo))
                        .collect();
                    rebuilt(node, children)
                }
                PackedNode::Ambiguity(alternatives) => {
                    let new = alternatives
                        .iter()
                        .map(|alternative| self.rename_binders(alternative, scope, renamed, memo))
                        .collect::<Vec<_>>();
                    if new
                        .iter()
                        .zip(alternatives)
                        .all(|(new, old)| Rc::ptr_eq(new, old))
                    {
                        Rc::clone(node)
                    } else {
                        PackedTerm::alternatives(new.into_iter().collect())
                    }
                }
            }
        });
        memo.insert(key, Rc::clone(&result));
        result
    }
}

/// `node`, a production node, over `children`; `node` itself when every child is its own.
fn rebuilt(node: &Rc<PackedTerm>, children: Vec<Rc<PackedTerm>>) -> Rc<PackedTerm> {
    match &node.node {
        PackedNode::Production {
            production,
            children: old,
            metadata,
        } => {
            if old
                .iter()
                .zip(&children)
                .all(|(old, new)| Rc::ptr_eq(old, new))
            {
                Rc::clone(node)
            } else {
                PackedTerm::production(*production, children, metadata.clone())
            }
        }
        PackedNode::InstantiatedProduction {
            production,
            parameters,
            children: old,
            metadata,
        } => {
            if old
                .iter()
                .zip(&children)
                .all(|(old, new)| Rc::ptr_eq(old, new))
            {
                Rc::clone(node)
            } else {
                PackedTerm::instantiated_production(
                    *production,
                    parameters.clone(),
                    children,
                    metadata.clone(),
                )
            }
        }
        PackedNode::Term(_) | PackedNode::Ambiguity(_) => {
            unreachable!("only a production node has children")
        }
    }
}

/// The name of the variable `term` is, under its annotations.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "every other node is no variable"
)]
fn variable_name_mut(term: &mut Term) -> Option<&mut String> {
    let mut term = term;
    loop {
        match term {
            Term::Annotated { term: inner, .. } => term = inner,
            Term::Variable { name, .. } => return Some(name),
            _ => return None,
        }
    }
}

/// `name` as written: without the mark and the number [`Grammar::scope_binders`] gave it.
fn written(name: &mut String) {
    if let Some(mark) = name.find(MARK) {
        name.truncate(mark);
    }
}

/// `term` with every variable a binder renamed apart named as written again.
pub(super) fn restore_term(mut term: Term) -> Term {
    let mut pending = vec![&mut term];
    // Invariant: every node of `term` not below a node of `pending` has its written name; each
    // iteration restores one node and schedules its children.
    while let Some(node) = pending.pop() {
        if let Some(name) = variable_name_mut(node) {
            written(name);
        }
        pending.extend(node.children_mut());
    }
    term
}

/// `text` with every name a binder renamed apart written again, in its own spelling and in the
/// `Debug` spelling of a string.
fn restore_text(text: &mut String) {
    if !text.contains(MARK) && !text.contains("\\u{e000}") {
        return;
    }
    let mut restored = String::with_capacity(text.len());
    let mut rest = text.as_str();
    // Invariant: `restored` followed by `rest` is the text with the marked suffixes before
    // `rest` removed.
    while !rest.is_empty() {
        let (skip, mark) = if let Some(after) = rest.strip_prefix(MARK) {
            (rest.len() - after.len(), true)
        } else if let Some(after) = rest.strip_prefix("\\u{e000}") {
            (rest.len() - after.len(), true)
        } else {
            (0, false)
        };
        if mark {
            rest = rest[skip..].trim_start_matches(|character: char| character.is_ascii_digit());
            continue;
        }
        let mut characters = rest.chars();
        let character = characters.next().expect("the rest is not empty");
        restored.push(character);
        rest = characters.as_str();
    }
    *text = restored;
}

/// `error` with every name a binder renamed apart written again in its texts. The other errors
/// hold no variable name: they are reported before inference, by the grammar, or of sorts.
#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "only the listed errors carry the text of a term or a variable"
)]
pub(super) fn restore_error(mut error: ParseError) -> ParseError {
    let restore_alternatives = |alternatives: &mut Vec<AmbiguousParse>| {
        for alternative in alternatives {
            restore_text(&mut alternative.term);
        }
    };
    match &mut error {
        ParseError::SortInference { message }
        | ParseError::RecordProduction { message }
        | ParseError::UserList { message } => restore_text(message),
        ParseError::InferenceEngineDisagreement { portable, z3, .. } => {
            for outcome in [portable, z3] {
                match outcome {
                    Ok(text) | Err(text) => restore_text(text),
                }
            }
        }
        ParseError::Ambiguous {
            alternatives,
            places,
            ..
        } => {
            restore_alternatives(alternatives);
            for AmbiguityPlace { alternatives, .. } in places {
                restore_alternatives(alternatives);
            }
        }
        _ => {}
    }
    error
}
