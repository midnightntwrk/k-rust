//! Scoped binders for sort inference.
//!
//! A quantifier `#Exists X . P` or `#Forall X . P` binds the variables of its binder in its body
//! and nowhere else (`kast::binding`), and a local function binds the variables of its pattern in
//! its own body (`#fun(P => B)(A)` and `#let P = A #in B` in `P` and `B`, not in `A`; the
//! lowering of `kompile::passes::resolve_fun` and the definition check's `term_position` read them
//! so). So the variable such a binder binds is a variable of its own, apart from every other
//! variable of the rule that has its spelling: the left side's `X`, a sibling binder's `X`, an
//! enclosing binder's `X`. Its sort is therefore inferred within its scope only, and a rule
//! infers exactly as the rule with that binder renamed apart does.
//!
//! The inference engines identify a variable by its name across a parse forest. So before
//! inference, [`Grammar::scope_binders`] renames each binder whose spelling stands for more than
//! one variable of the forest, with every occurrence it binds, to a new name: its name, [`MARK`]
//! and a number, chosen by a [`Reservation`] that holds every variable name of the parse, so the
//! new name is no name the rule writes, whatever spellings the definition's variable tokens
//! allow. The forest is then an alpha-variant of the parse, which every engine infers as a
//! whole. The [`Renaming`] records each new name with the name it replaces; after inference,
//! [`Renaming::restore_term`] gives exactly those variables their written names back, and
//! [`Renaming::restore_error`] does so in the texts of a rejection. A forest whose binders are
//! already apart is not changed, so neither is its inference.
//!
//! A quantifier's binder is identified by the span of its variable, and a local function's by the
//! span of the function, which are the same in every tree of the forest, so the trees of an
//! ambiguous parse agree on which variable each occurrence is.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::rc::Rc;

use crate::kast::binding::{Reservation, is_unresolved_anonymous, quantifier_kind};
use crate::kast::{InternalLabel, Term, TermSpan};

use super::forest::{PackedNode, PackedTerm};
use super::{AmbiguityPlace, AmbiguousParse, Grammar, ParseError};

/// The character between a binder's written name and the number of the name it is renamed to.
/// A name holding it can be written (a definition may declare variable tokens that spell it), so
/// it only makes the new names easy to tell apart; the [`Reservation`] makes them new.
const MARK: char = '\u{E000}';

/// Which binder an occurrence belongs to: the span of a quantifier's variable or of a local
/// function, or the identity of the node when it has no span.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Binder {
    Span(TermSpan),
    Node(*const PackedTerm),
}

/// The names the binders around a node bind there, each with its binder, innermost last.
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

/// A construct that binds names in some of its children.
struct Binding<'a> {
    /// The names it binds, each with its binder.
    names: Vec<(String, Binder)>,
    /// Its children, each with whether it lies in the scope of `names`.
    children: Vec<(&'a Rc<PackedTerm>, bool)>,
    /// Whether the occurrences of `names` in the children in scope are all walked, binders
    /// included (a local function's pattern), or the binder child holds binding occurrences that
    /// [`binder_variables`] reads (a quantifier's first child).
    quantifier: bool,
}

/// The local functions: `#fun2(P => B, A)`, `#fun3(P, B, A)` and `#let(P, A, B)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LocalFunction {
    Fun2,
    Fun3,
    Let,
}

impl Grammar {
    /// The label of the node `production` builds.
    fn node_labels(&self, production: usize) -> [Option<&crate::kast::Label>; 2] {
        let production = &self.productions[production];
        let node = production
            .term_production
            .map_or(production, |node| &self.productions[node]);
        [production.label.as_ref(), node.label.as_ref()]
    }

    /// Whether `production` builds a quantifier node: a production of `#Exists` or `#Forall` over
    /// a binder and a body.
    fn is_quantifier_production(&self, production: usize) -> bool {
        self.productions[production].nonterminals == 2
            && self
                .node_labels(production)
                .iter()
                .flatten()
                .any(|label| quantifier_kind(label).is_some())
    }

    /// The local function `production` builds, if it builds one.
    fn local_function_production(&self, production: usize) -> Option<LocalFunction> {
        let arity = self.productions[production].nonterminals;
        self.node_labels(production)
            .iter()
            .flatten()
            .find_map(|label| {
                if label.is(InternalLabel::Fun2) && arity == 2 {
                    Some(LocalFunction::Fun2)
                } else if label.is(InternalLabel::Fun3) && arity == 3 {
                    Some(LocalFunction::Fun3)
                } else if label.is(InternalLabel::Let) && arity == 3 {
                    Some(LocalFunction::Let)
                } else {
                    None
                }
            })
    }

    /// Whether `production` builds a rewrite `L => R`.
    fn is_rewrite_production(&self, production: usize) -> bool {
        self.productions[production].nonterminals == 2
            && self
                .node_labels(production)
                .iter()
                .flatten()
                .any(|label| label.is(InternalLabel::KRewrite))
    }

    /// The production and children of a production node.
    fn production_parts(node: &PackedTerm) -> Option<(usize, &[Rc<PackedTerm>])> {
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
            } => Some((*production, children)),
            PackedNode::Term(_) | PackedNode::Ambiguity(_) => None,
        }
    }

    /// What `node` binds, and where, when it is a quantifier or a local function node.
    fn binding<'a>(&self, node: &'a Rc<PackedTerm>) -> Option<Binding<'a>> {
        let (production, children) = Self::production_parts(node)?;
        if self.is_quantifier_production(production) {
            let [binder, body] = children else {
                return None;
            };
            return Some(Binding {
                names: binder_variables(binder),
                children: vec![(binder, true), (body, true)],
                quantifier: true,
            });
        }
        let function = self.local_function_production(production)?;
        let key = node
            .span()
            .map_or(Binder::Node(Rc::as_ptr(node)), Binder::Span);
        // The pattern binds in the function's own body; the argument (the bound value of a
        // `#let`) is evaluated in the enclosing term.
        let (pattern, in_scope): (&Rc<PackedTerm>, &[bool]) = match (function, children) {
            (LocalFunction::Fun2, [equation, _]) => (equation, &[true, false]),
            (LocalFunction::Fun3, [pattern, _, _]) => (pattern, &[true, true, false]),
            (LocalFunction::Let, [pattern, _, _]) => (pattern, &[true, false, true]),
            _ => return None,
        };
        let mut names = Vec::new();
        self.pattern_variables(pattern, &mut Vec::new(), &mut HashSet::new(), &mut names);
        Some(Binding {
            names: names.into_iter().map(|name| (name, key)).collect(),
            children: children.iter().zip(in_scope.iter().copied()).collect(),
            quantifier: false,
        })
    }

    /// Add to `found` the names of the variables at the binding positions of the local function
    /// equation or pattern `node`: every position outside the right side of a rewrite, less the
    /// names a quantifier inside it binds there (`excluded`), and not inside a nested local
    /// function, which is a scope of its own.
    fn pattern_variables(
        &self,
        node: &Rc<PackedTerm>,
        excluded: &mut Vec<String>,
        visited: &mut HashSet<(*const PackedTerm, Vec<String>)>,
        found: &mut Vec<String>,
    ) {
        if !visited.insert((Rc::as_ptr(node), excluded.clone())) {
            return;
        }
        crate::stack::guarded(|| match &node.node {
            PackedNode::Term(leaf) => {
                if let Term::Variable { name, .. } = leaf.unannotated()
                    && !is_unresolved_anonymous(name)
                    && !excluded.contains(name)
                    && !found.contains(name)
                {
                    found.push(name.clone());
                }
            }
            PackedNode::Ambiguity(alternatives) => {
                for alternative in alternatives {
                    self.pattern_variables(alternative, excluded, visited, found);
                }
            }
            PackedNode::Production {
                production,
                children,
                ..
            }
            | PackedNode::InstantiatedProduction {
                production,
                children,
                ..
            } => {
                if self.local_function_production(*production).is_some() {
                    return;
                }
                if self.is_rewrite_production(*production) {
                    self.pattern_variables(&children[0], excluded, visited, found);
                    return;
                }
                if self.is_quantifier_production(*production) {
                    let depth = excluded.len();
                    excluded.extend(
                        binder_variables(&children[0])
                            .into_iter()
                            .map(|(name, _)| name),
                    );
                    self.pattern_variables(&children[1], excluded, visited, found);
                    excluded.truncate(depth);
                    return;
                }
                for child in children {
                    self.pattern_variables(child, excluded, visited, found);
                }
            }
        });
    }

    /// Each of `forests`, the readings of one parse, with every binder that shares its spelling
    /// with another variable of that forest renamed apart, with the occurrences it binds (module
    /// docs), or `None` where every binder is apart already (the forest of every rule without
    /// quantifiers or local functions among them); and the new names.
    pub(super) fn scope_binders(
        &self,
        forests: &[&Rc<PackedTerm>],
    ) -> (Vec<Option<Rc<PackedTerm>>>, Renaming) {
        let shared = forests
            .iter()
            .map(|forest| {
                let mut identities: BTreeMap<String, BTreeSet<Identity>> = BTreeMap::new();
                self.collect_identities(
                    forest,
                    &mut Scope::new(),
                    &mut HashSet::new(),
                    &mut identities,
                );
                identities.retain(|_, identities| identities.len() >= 2);
                identities
            })
            .collect::<Vec<_>>();
        let mut renaming = Renaming::default();
        if shared.iter().all(BTreeMap::is_empty) {
            return (vec![None; forests.len()], renaming);
        }
        let mut minter = Minter::new(self, forests);
        let scoped = forests
            .iter()
            .zip(shared)
            .map(|(forest, shared)| {
                let mut renamed: HashMap<(String, Binder), String> = HashMap::new();
                for (name, identities) in shared {
                    for binder in identities.into_iter().flatten() {
                        let new = minter.mint(&name);
                        renaming.written.insert(new.clone(), name.clone());
                        renamed.insert((name.clone(), binder), new);
                    }
                }
                (!renamed.is_empty()).then(|| {
                    self.rename_binders(forest, &mut Scope::new(), &renamed, &mut HashMap::new())
                })
            })
            .collect();
        (scoped, renaming)
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
            if let Some(binding) = self.binding(node) {
                let depth = scope.len();
                for (name, key) in &binding.names {
                    identities
                        .entry(name.clone())
                        .or_default()
                        .insert(Some(*key));
                }
                for (index, (child, in_scope)) in binding.children.iter().enumerate() {
                    // A quantifier's binder holds only binding occurrences, recorded above.
                    if binding.quantifier && index == 0 {
                        continue;
                    }
                    if *in_scope {
                        scope.extend(binding.names.iter().cloned());
                    }
                    self.collect_identities(child, scope, visited, identities);
                    scope.truncate(depth);
                }
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
            if let Some(binding) = self.binding(node) {
                let depth = scope.len();
                let names = binding
                    .names
                    .iter()
                    .filter(|(name, key)| renamed.contains_key(&(name.clone(), *key)))
                    .cloned()
                    .collect::<Vec<_>>();
                // A binder's own variables are in the scope of its new names.
                let children = binding
                    .children
                    .iter()
                    .map(|(child, in_scope)| {
                        if *in_scope {
                            scope.extend(names.iter().cloned());
                        }
                        let child = self.rename_binders(child, scope, renamed, memo);
                        scope.truncate(depth);
                        child
                    })
                    .collect();
                return rebuilt(node, children);
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

/// The source of the new names of [`Grammar::scope_binders`] over the forests of one parse.
struct Minter {
    /// Every variable name of the forests and every name minted so far.
    reserved: Reservation,
    /// The texts of the forests' leaves and labels, in their own and their `Debug` spellings,
    /// which no new name occurs in, so [`Renaming::restore_error`] can find the new names in a
    /// rejection's text without touching what the rule writes.
    texts: Vec<String>,
}

impl Minter {
    fn new(grammar: &Grammar, forests: &[&Rc<PackedTerm>]) -> Self {
        let mut reserved = Reservation::new();
        let mut texts = BTreeSet::new();
        for forest in forests {
            forest_texts(grammar, forest, &mut reserved, &mut texts);
        }
        Self {
            reserved,
            texts: texts.into_iter().collect(),
        }
    }

    /// A new name for a binder written `name`: `name`, [`MARK`] and a number, the first such name
    /// that is no variable name of the forests, no name minted before, and occurs in no text of
    /// the forests.
    fn mint(&mut self, name: &str) -> String {
        let stem = format!("{name}{MARK}");
        // Invariant: every name tried before is reserved, and the reservation mints a name not
        // tried before at each step; the texts are finite, so a name in none of them is reached.
        loop {
            let candidate = self.reserved.mint(&stem);
            let debug = debug_spelling(&candidate);
            if !self
                .texts
                .iter()
                .any(|text| text.contains(&candidate) || text.contains(&debug))
            {
                return candidate;
            }
        }
    }
}

/// The new names [`Grammar::scope_binders`] gave binders over the forests of one parse, each
/// with the written name it replaces.
#[derive(Debug, Default)]
pub(super) struct Renaming {
    written: BTreeMap<String, String>,
}

impl Renaming {
    /// Whether no binder was renamed.
    pub(super) fn is_empty(&self) -> bool {
        self.written.is_empty()
    }

    /// `term` with every variable a binder renamed apart named as written again.
    pub(super) fn restore_term(&self, mut term: Term) -> Term {
        let mut pending = vec![&mut term];
        // Invariant: every node of `term` not below a node of `pending` has its written name;
        // each iteration restores one node and schedules its children.
        while let Some(node) = pending.pop() {
            if let Some(name) = variable_name_mut(node)
                && let Some(written) = self.written.get(name.as_str())
            {
                name.clone_from(written);
            }
            pending.extend(node.children_mut());
        }
        term
    }

    /// `text` with every new name written again, in its own spelling and in the `Debug` spelling
    /// of a string. A new name occurs in no text of the forests, so each occurrence of one is
    /// that name; where one new name is part of another, the longer is read.
    fn restore_text(&self, text: &mut String) {
        if !text.contains(MARK) && !text.contains("\\u{e000}") {
            return;
        }
        let mut spellings = Vec::with_capacity(self.written.len() * 2);
        for (new, written) in &self.written {
            spellings.push((new.clone(), written.clone()));
            spellings.push((debug_spelling(new), debug_spelling(written)));
        }
        spellings.sort_by_key(|(new, _)| std::cmp::Reverse(new.len()));
        let mut restored = String::with_capacity(text.len());
        let mut rest = text.as_str();
        // Invariant: `restored` followed by `rest` is the text with the new names before `rest`
        // written again.
        while let Some(character) = rest.chars().next() {
            if let Some((new, written)) = spellings
                .iter()
                .find(|(new, _)| rest.starts_with(new.as_str()))
            {
                restored.push_str(written);
                rest = &rest[new.len()..];
            } else {
                restored.push(character);
                rest = &rest[character.len_utf8()..];
            }
        }
        *text = restored;
    }

    /// `error` with every new name written again in its texts. The other errors hold no
    /// variable name: they are reported before inference, by the grammar, or of sorts.
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "only the listed errors carry the text of a term or a variable"
    )]
    pub(super) fn restore_error(&self, mut error: ParseError) -> ParseError {
        let restore_alternatives = |alternatives: &mut Vec<AmbiguousParse>| {
            for alternative in alternatives {
                self.restore_text(&mut alternative.term);
            }
        };
        match &mut error {
            ParseError::SortInference { message }
            | ParseError::RecordProduction { message }
            | ParseError::UserList { message } => self.restore_text(message),
            ParseError::InferenceEngineDisagreement { portable, z3, .. } => {
                for outcome in [portable, z3] {
                    match outcome {
                        Ok(text) | Err(text) => self.restore_text(text),
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
}

/// `name` as the `Debug` spelling of a string writes it, without the quotes.
fn debug_spelling(name: &str) -> String {
    let debug = format!("{name:?}");
    debug[1..debug.len() - 1].to_owned()
}

/// Reserve every variable name of `forest`, and add to `texts` the text of every leaf and the
/// name of every production label of it, each in its own and its `Debug` spelling.
fn forest_texts(
    grammar: &Grammar,
    forest: &Rc<PackedTerm>,
    reserved: &mut Reservation,
    texts: &mut BTreeSet<String>,
) {
    let mut visited = HashSet::new();
    let mut pending = vec![Rc::clone(forest)];
    let add = |text: String, texts: &mut BTreeSet<String>| {
        texts.insert(debug_spelling(&text));
        texts.insert(text);
    };
    // Invariant: `visited` holds the nodes already read and `pending` reachable nodes not yet
    // read; each node is read once.
    while let Some(node) = pending.pop() {
        if !visited.insert(Rc::as_ptr(&node)) {
            continue;
        }
        match &node.node {
            PackedNode::Term(leaf) => {
                leaf.visit_preorder(&mut |part| match part {
                    Term::Variable { name, .. } => {
                        reserved.reserve(name.clone());
                        add(name.clone(), texts);
                    }
                    Term::Token { token, .. } => add(token.clone(), texts),
                    Term::Apply { label, .. } => add(label.name.clone(), texts),
                    Term::InjectedLabel(label) => add(label.name.clone(), texts),
                    Term::Annotated { .. }
                    | Term::Rewrite { .. }
                    | Term::As { .. }
                    | Term::Sequence(_) => {}
                });
            }
            PackedNode::Production {
                production,
                children,
                ..
            }
            | PackedNode::InstantiatedProduction {
                production,
                children,
                ..
            } => {
                for label in grammar.node_labels(*production).into_iter().flatten() {
                    add(label.name.clone(), texts);
                }
                pending.extend(children.iter().cloned());
            }
            PackedNode::Ambiguity(alternatives) => pending.extend(alternatives.iter().cloned()),
        }
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Only the new names are written again in a rejection's text, in their own and their
    /// `Debug` spellings, the longer of two that overlap first; a written name that holds the
    /// mark, or spells a new name's stem with other digits, is left alone.
    #[test]
    fn a_rejection_text_writes_again_exactly_the_new_names() {
        let renaming = Renaming {
            written: [
                ("Y\u{E000}1", "Y"),
                ("XY\u{E000}0", "XY"),
                ("?A\u{E000}0", "?A"),
            ]
            .into_iter()
            .map(|(new, written)| (new.to_owned(), written.to_owned()))
            .collect(),
        };
        let mut text = "Y\u{E000}1 Z\u{E000}5 XY\u{E000}0 \"Y\\u{e000}1\" Y\u{E000}0 ?A\u{E000}0:Int Y\u{E000}2"
            .to_owned();
        renaming.restore_text(&mut text);
        assert_eq!(text, "Y Z\u{E000}5 XY \"Y\" Y\u{E000}0 ?A:Int Y\u{E000}2");
        let error = renaming.restore_error(ParseError::SortInference {
            message: "variable Z\u{E000}5 beside Y\u{E000}1".to_owned(),
        });
        assert!(
            matches!(&error, ParseError::SortInference { message } if message == "variable Z\u{E000}5 beside Y"),
            "{error:?}"
        );
    }

    /// The `Debug` spelling of a name is the text between the quotes of its string's.
    #[test]
    fn the_debug_spelling_escapes_the_mark() {
        assert_eq!(debug_spelling("Y\u{E000}0"), "Y\\u{e000}0");
        assert_eq!(debug_spelling("?X"), "?X");
    }
}
