//! ```toml algorithm-site
//! id = "kompile.sort_injections.insert"
//! role = "variant"
//! sites = ["SentenceTyper::typing", "SentenceTyper::typing_of", "Walk::visit", "Walk::injected", "Walk::projected"]
//! ```
//!
//! A read-only typing view of a loaded rule-like sentence, computed by the sort injector on the
//! sentence as compilation hands it to injection: semantic casts resolved, and a body with a
//! rewrite projected into its left and right branches.
//!
//! Cost: the body is walked at most four times (a sort walk and a placement walk per branch of a
//! body with a rewrite, one of each otherwise) and the conditions once. At every node the walk
//! names the node's path by its node in a trie the walks share (`PathTrie`, constant time per
//! step), types the resolved subterm there in place, and asks the injector for the node's sort
//! and placement as injection does, the injector inferring each node's sort once per expected
//! sort over the whole typing (`NaturalSorts`). Only a node above a rewrite (or, in the right
//! branch, above an as-pattern) is typed on a projected copy of its subterm
//! (`Walk::projected`). For N nodes, k of them above a rewrite, of height h, that is
//! O(N x (P + S) + k x h) with the injector's P and S, plus the parametric instance searches
//! and one semantic-cast resolution of the sentence; reading every path back out of the typing
//! (`PathMap::iter`) costs O(N x h). `kompile.macros.expand` computes this view once per rewrite of a
//! sentence when some macro rule has a parametric head.

use std::borrow::Cow;
use std::cell::Cell;
use std::collections::BTreeMap;
use std::fmt;

use crate::definition::{
    AttributeKey, Attributes, PartialOrder, ProductionItem, ResolvedDefinition, Sentence,
};
use crate::kast::parser::parse_sort_text;
use crate::kast::{GeneratedLabel, InternalLabel, Sort, Term};
use crate::kompile::passes::{
    ResolveSemanticCastsError, resolve_semantic_casts_in_sentence, semantic_cast_variable_sorts,
    with_kitem_subsorts,
};
use crate::kompile::view::View;
use crate::names::BuiltinSort;

use super::{
    SortInjectionError, SortInjector, SortMismatch, has_rewrite, render_term, rewrite_projection,
};

/// The sorts at one position of a sentence.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PositionTyping {
    /// The sort compilation places the term at the position at, or `None` for syntax that has no
    /// sort (the `#cells` wrapper, `#dots`, `#noDots`) and for a variable nothing types.
    pub sort: Option<Sort>,
    /// The sort the position requires of its term, or `None` where compilation places no sort
    /// requirement (a body without a rewrite, a child of a syntax-only term).
    pub required: Option<Sort>,
}

/// The typing of a position in the two branches compilation types a body with a rewrite in:
/// the left branch has every rewrite replaced by its left side, the right branch by its right side
/// (and every as-pattern by its alias).
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BranchTyping {
    pub left: PositionTyping,
    pub right: PositionTyping,
}

/// The typing of one rule-like sentence, as compilation computes it.
///
/// Paths are those of [`crate::provenance::DestinationAnchor::path`]: the first step selects the
/// sentence field (0 body, 1 requires, 2 ensures), and each further step selects a child: the
/// left (0) or right (1) side of a rewrite, the pattern (0) or alias (1) of an as-pattern, an
/// application's argument (semantic casts included), or a sequence item. Annotations are
/// transparent.
///
/// A path typed identically wherever compilation types it is in `positions`. A path of a body
/// with a rewrite that lies above a rewrite, or is a rewrite, is typed once per branch; when the
/// two typings differ (the rewrite's own node, an application whose instantiation depends on the
/// side), the path is in `branches` instead. A path inside one side of a rewrite, or the pattern
/// of an as-pattern, exists in one branch only and is in `positions`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SentenceTyping {
    pub positions: PathMap<PositionTyping>,
    pub branches: PathMap<BranchTyping>,
    /// The sort of each named variable that semantic-cast resolution determines.
    pub variables: BTreeMap<String, Sort>,
    /// The instance injection gives the label of each application of a parametric production,
    /// one entry per sort parameter (`None` where it leaves the parameter open). A path typed
    /// with different instances in the two branches of a rewrite has no entry.
    pub(crate) instances: PathMap<Vec<Option<Sort>>>,
}

/// The paths of one sentence's positions, interned as a trie: node 0 is the empty path, and each
/// other node is its parent's path extended by one step. A walk that descends one step at a
/// time names each position by its node in constant time, so a typing of N positions takes
/// O(N) memory rather than one path, as long as its depth, per position.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PathTrie {
    /// The parent and the last step of each node but the root.
    parents: Vec<(usize, u32)>,
    /// The children of each node, by step, in ascending order of step.
    children: Vec<Vec<(u32, usize)>>,
}

impl PathTrie {
    fn new() -> Self {
        Self {
            parents: vec![(0, 0)],
            children: vec![Vec::new()],
        }
    }

    fn len(&self) -> usize {
        self.children.len()
    }

    /// The node of `node`'s path extended by `step`, added when it is new.
    fn child(&mut self, node: usize, step: u32) -> usize {
        match self.children[node].binary_search_by_key(&step, |(step, _)| *step) {
            Ok(index) => self.children[node][index].1,
            Err(index) => {
                let child = self.children.len();
                self.children.push(Vec::new());
                self.parents.push((node, step));
                self.children[node].insert(index, (step, child));
                child
            }
        }
    }

    fn find_child(&self, node: usize, step: u32) -> Option<usize> {
        self.children[node]
            .binary_search_by_key(&step, |(step, _)| *step)
            .ok()
            .map(|index| self.children[node][index].1)
    }

    fn find(&self, path: &[u32]) -> Option<usize> {
        path.iter()
            .try_fold(0, |node, step| self.find_child(node, *step))
    }

    fn path(&self, mut node: usize) -> Vec<u32> {
        let mut path = Vec::new();
        while node != 0 {
            let (parent, step) = self.parents[node];
            path.push(step);
            node = parent;
        }
        path.reverse();
        path
    }

    /// Every node, each before its descendants and children in ascending order of step: the
    /// order of their paths.
    fn preorder(&self) -> Vec<usize> {
        let mut order = Vec::with_capacity(self.len());
        let mut pending = vec![0];
        while let Some(node) = pending.pop() {
            order.push(node);
            pending.extend(self.children[node].iter().rev().map(|(_, child)| *child));
        }
        order
    }
}

/// A map from the paths of a sentence's positions to values, over a [`PathTrie`] the maps of
/// one typing share. Paths are compared and ordered as the step sequences they are.
#[derive(Clone)]
pub struct PathMap<V> {
    trie: std::sync::Arc<PathTrie>,
    values: Vec<Option<V>>,
    len: usize,
}

impl<V> Default for PathMap<V> {
    fn default() -> Self {
        Self::over(std::sync::Arc::new(PathTrie::new()), Vec::new())
    }
}

impl<V> PathMap<V> {
    /// The map of `values`, indexed by the nodes of `trie`.
    fn over(trie: std::sync::Arc<PathTrie>, mut values: Vec<Option<V>>) -> Self {
        values.resize_with(trie.len(), || None);
        let len = values.iter().filter(|value| value.is_some()).count();
        Self { trie, values, len }
    }

    pub fn get(&self, path: &[u32]) -> Option<&V> {
        self.trie
            .find(path)
            .and_then(|node| self.values[node].as_ref())
    }

    pub fn get_mut(&mut self, path: &[u32]) -> Option<&mut V> {
        self.trie
            .find(path)
            .and_then(|node| self.values[node].as_mut())
    }

    pub fn contains_key(&self, path: &[u32]) -> bool {
        self.get(path).is_some()
    }

    pub fn insert(&mut self, path: Vec<u32>, value: V) -> Option<V> {
        let trie = std::sync::Arc::make_mut(&mut self.trie);
        let node = path.iter().fold(0, |node, step| trie.child(node, *step));
        self.values.resize_with(trie.len(), || None);
        let previous = self.values[node].replace(value);
        self.len += usize::from(previous.is_none());
        previous
    }

    pub fn remove(&mut self, path: &[u32]) -> Option<V> {
        let removed = self
            .trie
            .find(path)
            .and_then(|node| self.values[node].take());
        self.len -= usize::from(removed.is_some());
        removed
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Every path with its value, in the order of the paths.
    pub fn iter(&self) -> impl Iterator<Item = (Vec<u32>, &V)> + '_ {
        self.trie.preorder().into_iter().filter_map(|node| {
            self.values[node]
                .as_ref()
                .map(|value| (self.trie.path(node), value))
        })
    }

    pub fn keys(&self) -> impl Iterator<Item = Vec<u32>> + '_ {
        self.iter().map(|(path, _)| path)
    }

    pub fn values(&self) -> impl Iterator<Item = &V> + '_ {
        self.iter().map(|(_, value)| value)
    }
}

impl<V> Extend<(Vec<u32>, V)> for PathMap<V> {
    fn extend<I: IntoIterator<Item = (Vec<u32>, V)>>(&mut self, entries: I) {
        for (path, value) in entries {
            self.insert(path, value);
        }
    }
}

impl<V> FromIterator<(Vec<u32>, V)> for PathMap<V> {
    fn from_iter<I: IntoIterator<Item = (Vec<u32>, V)>>(entries: I) -> Self {
        let mut map = Self::default();
        map.extend(entries);
        map
    }
}

impl<'a, V> IntoIterator for &'a PathMap<V> {
    type Item = (Vec<u32>, &'a V);
    type IntoIter = Box<dyn Iterator<Item = (Vec<u32>, &'a V)> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.iter())
    }
}

impl<V: PartialEq> PartialEq for PathMap<V> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other.iter())
    }
}

impl<V: Eq> Eq for PathMap<V> {}

impl<V: fmt::Debug> fmt::Debug for PathMap<V> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_map().entries(self.iter()).finish()
    }
}

impl SentenceTyping {
    /// The typing at `path` when it is the same in every branch.
    pub fn at(&self, path: &[u32]) -> Option<&PositionTyping> {
        self.positions.get(path)
    }
}

/// Why a sentence has no typing: the same errors compilation reports for it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SentenceTypingError {
    /// The sentence is not a rule or claim.
    NotRuleLike,
    /// The module is not in the definition.
    MissingModule(String),
    /// The variables' sort annotations and casts disagree.
    SemanticCasts(ResolveSemanticCastsError),
    /// A term is ill-sorted at its position, a cast is incomparable with its operand, or a
    /// production cannot be instantiated; `location` is the sentence's `source:line` when known.
    Sort {
        location: Option<String>,
        error: SortInjectionError,
    },
}

impl fmt::Display for SentenceTypingError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotRuleLike => write!(formatter, "only rules and claims have a typing view"),
            Self::MissingModule(module) => write!(formatter, "module {module:?} was not found"),
            Self::SemanticCasts(error) => error.fmt(formatter),
            Self::Sort { location, error } => {
                if let Some(location) = location {
                    write!(formatter, "{location}: ")?;
                }
                error.fmt(formatter)
            }
        }
    }
}

impl std::error::Error for SentenceTypingError {}

/// The typing of `sentence`, a rule or claim of `module`, at the loaded layer.
///
/// Equivalent to `SentenceTyper::new(definition, module)?.typing(sentence)`; build a
/// [`SentenceTyper`] once to type several sentences of one module.
pub fn sentence_typing(
    definition: &ResolvedDefinition,
    module: &str,
    sentence: &Sentence,
) -> Result<SentenceTyping, SentenceTypingError> {
    SentenceTyper::new(definition, module)?.typing(sentence)
}

/// Types the loaded rule-like sentences of one module.
///
/// The typing is a read of compilation's own computation. Semantic casts are resolved by the
/// resolution pass (its variable sorts and errors), a body with a rewrite is projected into its
/// branches as injection projects it, and every sort and requirement comes from the injector on
/// that resolved and projected term: the sort it places a term at (an upcast's operand sort),
/// a production's instantiated argument sorts (the selected overload,
/// the joint parametric solver), the least upper bound of a rewrite's branches, the sort of an
/// as-pattern's sides, sequence items at `KItem` or `K`, and conditions at `Bool`. Each term is
/// checked at its position with the injector's decision (one injection, the `K` sequence, the
/// sequence injected above `K`, or a collection or user-list wrapper), so a sentence compilation
/// rejects for an ill-sorted term, a cast that is not an upcast, an ambiguous instantiation, or
/// disagreeing variable annotations returns that error here.
///
/// The injector runs after cell concretization, which a loaded sentence has not had; the view
/// keeps the loaded shapes: `#cells`, `#dots` and `#noDots` have no sort and place no
/// requirement, an authored cell `L(#dots|#noDots, body, #dots|#noDots)` has its production's
/// sort and places its body at the cell's single content sort, and a loaded `project:S` is typed
/// as `S ::= project:S(K)`. It types in the order injection runs in, where every non-parser sort
/// is declared below `KItem`.
///
/// The view does not infer: a variable nothing types reports no sort, though its position still
/// reports its requirement. A cast's operand reports the cast's sort as its requirement.
pub struct SentenceTyper<'a> {
    injector: SortInjector<'a, 'a>,
    declared: PartialOrder<Sort>,
}

impl<'a> SentenceTyper<'a> {
    pub fn new(
        definition: &'a ResolvedDefinition,
        module: &str,
    ) -> Result<Self, SentenceTypingError> {
        let module_id = definition
            .module_id(module)
            .ok_or_else(|| SentenceTypingError::MissingModule(module.to_owned()))?;
        let cycle = |cycle: crate::definition::PartialOrderCycle<Sort>| SentenceTypingError::Sort {
            location: None,
            error: SortInjectionError::CircularSubsort(cycle.path),
        };
        let sorts = definition.sort_catalog(module_id);
        let declared = definition.subsorts(module_id).map_err(cycle)?;
        let subsorts = with_kitem_subsorts(&declared, sorts.all_sorts()).map_err(cycle)?;
        Ok(Self {
            injector: SortInjector {
                productions: View::Shared(definition.production_catalog(module_id)),
                sorts: View::Owned(sorts),
                subsorts: View::Owned(subsorts),
                next_sort_parameter: Cell::new(0),
                natural_sorts: std::cell::RefCell::default(),
            },
            declared,
        })
    }

    pub fn typing(&self, sentence: &Sentence) -> Result<SentenceTyping, SentenceTypingError> {
        self.typing_at(sentence, None)
    }

    /// Type a ground value at the position from which its emitted instance is inferred.
    pub(crate) fn ground_typing(
        &self,
        term: &Term,
        position: &Sort,
    ) -> Result<SentenceTyping, SentenceTypingError> {
        self.typing_at(
            &Sentence::Rule {
                body: term.clone(),
                requires: Term::Token {
                    token: "true".into(),
                    sort: Sort::builtin(BuiltinSort::Bool),
                },
                ensures: Term::Token {
                    token: "true".into(),
                    sort: Sort::builtin(BuiltinSort::Bool),
                },
                attributes: Attributes::default(),
            },
            Some(position),
        )
    }

    fn typing_at(
        &self,
        sentence: &Sentence,
        top: Option<&Sort>,
    ) -> Result<SentenceTyping, SentenceTypingError> {
        let (Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        }) = sentence
        else {
            return Err(SentenceTypingError::NotRuleLike);
        };
        let location =
            sentence
                .attributes()
                .source()
                .map(|source| match sentence.attributes().location() {
                    Some(location) => format!("{source}:{}", location.start_line),
                    None => source.to_owned(),
                });
        crate::definition::checks::reject_label_parameters(sentence).map_err(|error| {
            SentenceTypingError::Sort {
                location: location.clone(),
                error: SortInjectionError::label_parameters(error),
            }
        })?;
        let variables = semantic_cast_variable_sorts(sentence, &self.declared)
            .map_err(SentenceTypingError::SemanticCasts)?;
        let resolved = resolve_semantic_casts_in_sentence(&self.declared, sentence.clone())
            .map_err(SentenceTypingError::SemanticCasts)?;
        let (Sentence::Rule {
            body: resolved_body,
            requires: resolved_requires,
            ensures: resolved_ensures,
            ..
        }
        | Sentence::Claim {
            body: resolved_body,
            requires: resolved_requires,
            ensures: resolved_ensures,
            ..
        }) = &resolved
        else {
            unreachable!("resolution keeps the sentence kind")
        };
        self.typing_of(
            [body, requires, ensures],
            [resolved_body, resolved_requires, resolved_ensures],
            variables,
            top,
        )
        .map_err(|error| SentenceTypingError::Sort { location, error })
    }

    fn typing_of(
        &self,
        loaded: [&Term; 3],
        resolved: [&Term; 3],
        variables: BTreeMap<String, Sort>,
        top: Option<&Sort>,
    ) -> Result<SentenceTyping, SortInjectionError> {
        let injector = &self.injector;
        injector.next_sort_parameter.set(0);
        // Every term the walks type is a node of `resolved`, or a projection built for one and
        // typed outside the memo, so the injector's sort memo holds for the whole typing.
        injector.memoized(|| self.typing_with_memo(loaded, resolved, variables, top))
    }

    fn typing_with_memo(
        &self,
        loaded: [&Term; 3],
        resolved: [&Term; 3],
        variables: BTreeMap<String, Sort>,
        top: Option<&Sort>,
    ) -> Result<SentenceTyping, SortInjectionError> {
        let injector = &self.injector;
        let top = top
            .cloned()
            .unwrap_or_else(|| injector.fresh_sort_parameter());
        let boolean = Sort::builtin(BuiltinSort::Bool);
        let mut trie = PathTrie::new();
        let projections = Projections::of(resolved[0]);

        let mut conditions = Walk::new(injector, Branch::Only, &mut trie, &projections);
        for (field, loaded, resolved) in
            [(1u32, loaded[1], resolved[1]), (2, loaded[2], resolved[2])]
        {
            let mut path = Cursor::root();
            path.push(conditions.trie, field);
            let slot = conditions.visit(loaded, resolved, &mut path, &boolean)?;
            conditions.place(&path, &slot, &boolean)?;
        }
        let (mut positions, mut instances) = conditions.finish();
        // As `inject_rule_body`: a body with a rewrite is the rewrite of its two projections,
        // typed at their least upper bound below the top hint, and each projection is
        // injected at that bound; a body without one is typed below the top hint and
        // injected at its own sort. The body's sort comes from a first walk (the injector's
        // `term_sort` cannot type loaded cell fragments), and the second walk types the body at
        // the position injection places it at.
        let branches: &[Branch] = if has_rewrite(resolved[0]) {
            &[Branch::Left, Branch::Right]
        } else {
            &[Branch::Only]
        };
        let body = |trie: &mut PathTrie| {
            let mut path = Cursor::root();
            path.push(trie, 0);
            path
        };
        let mut sorts = Vec::new();
        for branch in branches {
            let mut walk = Walk::new(injector, *branch, &mut trie, &projections);
            let mut path = body(walk.trie);
            sorts.extend(walk.visit(loaded[0], resolved[0], &mut path, &top)?.sort);
        }
        let position = match branches {
            [Branch::Only] => sorts.first().cloned(),
            _ if sorts.is_empty() => None,
            _ => Some(injector.least_upper_bound(&sorts, Some(&top))?),
        };
        let mut maps = Vec::new();
        let mut branch_instances = Vec::new();
        for branch in branches {
            let mut walk = Walk::new(injector, *branch, &mut trie, &projections);
            let mut path = body(walk.trie);
            let hint = position.clone().unwrap_or_else(|| top.clone());
            let slot = walk.visit(loaded[0], resolved[0], &mut path, &hint)?;
            if *branch != Branch::Only
                && let Some(position) = &position
            {
                walk.place(&path, &slot, position)?;
            }
            let (positions, instances) = walk.finish();
            maps.push(positions);
            branch_instances.push(instances);
        }
        // The walks name positions by the nodes of one trie, so the branches' typings of a
        // position are merged by node.
        let mut branch_typings = Vec::new();
        let first = maps.remove(0);
        match maps.pop() {
            None => merge_into(&mut positions, first),
            Some(right) => {
                let mut left = first;
                for (node, right) in right.into_iter().enumerate() {
                    let Some(right) = right else {
                        continue;
                    };
                    let left = left.get_mut(node).and_then(Option::take);
                    match left {
                        Some(left) if left == right => set(&mut positions, node, left),
                        Some(left) => branch_typings.push((node, BranchTyping { left, right })),
                        None => set(&mut positions, node, right),
                    }
                }
                merge_into(&mut positions, left);
            }
        }
        let first = branch_instances.remove(0);
        match branch_instances.pop() {
            None => merge_into(&mut instances, first),
            Some(right) => {
                let mut left = first;
                for (node, right) in right.into_iter().enumerate() {
                    let Some(right) = right else {
                        continue;
                    };
                    match left.get_mut(node).and_then(Option::take) {
                        Some(left) if left != right => {}
                        _ => set(&mut instances, node, right),
                    }
                }
                merge_into(&mut instances, left);
            }
        }
        let trie = std::sync::Arc::new(trie);
        let mut branches = Vec::new();
        for (node, typing) in branch_typings {
            set(&mut branches, node, typing);
        }
        Ok(SentenceTyping {
            positions: PathMap::over(std::sync::Arc::clone(&trie), positions),
            branches: PathMap::over(std::sync::Arc::clone(&trie), branches),
            variables,
            instances: PathMap::over(trie, instances),
        })
    }
}

/// Values by trie node.
type NodeValues<V> = Vec<Option<V>>;

fn set<V>(values: &mut NodeValues<V>, node: usize, value: V) {
    if values.len() <= node {
        values.resize_with(node + 1, || None);
    }
    values[node] = Some(value);
}

/// Add each value of `from` to `into` at its node.
fn merge_into<V>(into: &mut NodeValues<V>, from: NodeValues<V>) {
    for (node, value) in from.into_iter().enumerate() {
        if let Some(value) = value {
            set(into, node, value);
        }
    }
}

/// The current path of a walk, as the trie nodes of its prefixes.
struct Cursor {
    nodes: Vec<usize>,
}

impl Cursor {
    fn root() -> Self {
        Self { nodes: vec![0] }
    }

    fn node(&self) -> usize {
        *self.nodes.last().expect("a cursor holds the root")
    }

    fn push(&mut self, trie: &mut PathTrie, step: u32) {
        let node = trie.child(self.node(), step);
        self.nodes.push(node);
    }

    fn pop(&mut self) {
        self.nodes.pop();
    }
}

/// The nodes of a rule body under which the rewrite projection changes something: those that
/// are or contain a rewrite (both branches), and those that are or contain an as-pattern (the
/// right branch, which keeps an as-pattern's alias). A node outside them is its own projection,
/// so the walk types it in place rather than on a copy. Nodes are named by address; the body is
/// borrowed for the whole typing.
struct Projections {
    rewrites: std::collections::HashSet<usize>,
    rewrites_or_aliases: std::collections::HashSet<usize>,
}

impl Projections {
    fn of(body: &Term) -> Self {
        let mut rewrites = std::collections::HashSet::new();
        let mut rewrites_or_aliases = std::collections::HashSet::new();
        // Post-order with an explicit stack: a node is visited after its children.
        let mut pending = vec![(body, false)];
        let mut flags: Vec<(bool, bool)> = Vec::new();
        // Invariant: `flags` holds, for each child of a node whose children were all visited,
        // whether it contains a rewrite and whether it contains a rewrite or an as-pattern.
        while let Some((term, visited)) = pending.pop() {
            let children = immediate_children(term);
            if !visited {
                pending.push((term, true));
                pending.extend(children.iter().rev().map(|child| (*child, false)));
                continue;
            }
            let mut rewrite = matches!(term, Term::Rewrite { .. });
            let mut either = rewrite || matches!(term, Term::As { .. });
            for (child_rewrite, child_either) in flags.split_off(flags.len() - children.len()) {
                rewrite |= child_rewrite;
                either |= child_either;
            }
            let address = std::ptr::from_ref(term) as usize;
            if rewrite {
                rewrites.insert(address);
            }
            if either {
                rewrites_or_aliases.insert(address);
            }
            flags.push((rewrite, either));
        }
        Self {
            rewrites,
            rewrites_or_aliases,
        }
    }

    /// Whether projecting `term`, a node of the body, for the branch `right` selects changes it.
    fn changes(&self, term: &Term, right: bool) -> bool {
        let address = std::ptr::from_ref(term) as usize;
        if right {
            self.rewrites_or_aliases.contains(&address)
        } else {
            self.rewrites.contains(&address)
        }
    }
}

/// The direct subterms of `term`, an annotation's term included.
fn immediate_children(term: &Term) -> Vec<&Term> {
    match term {
        Term::Annotated { term, .. } => vec![term],
        Term::Rewrite { left, right } => vec![left, right],
        Term::As { pattern, alias } => vec![pattern, alias],
        Term::Sequence(items)
        | Term::Apply {
            arguments: items, ..
        } => items.iter().collect(),
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => Vec::new(),
    }
}

/// Which projection of the body a walk types.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Branch {
    /// A condition, or a body without a rewrite.
    Only,
    Left,
    Right,
}

/// The term occupying a position in compilation, and the sort injection places it at.
struct Slot<'r> {
    /// The resolved and projected term at the position: the resolved node itself where the
    /// projection leaves it unchanged, else its projection.
    term: Cow<'r, Term>,
    /// The sort injection places it at; `None` for syntax without a sort.
    sort: Option<Sort>,
}

struct Walk<'a, 'view, 'definition, 't> {
    injector: &'a SortInjector<'view, 'definition>,
    branch: Branch,
    /// The paths of the typing's positions; the walk's values are indexed by its nodes.
    trie: &'t mut PathTrie,
    projections: &'t Projections,
    positions: NodeValues<PositionTyping>,
    instances: NodeValues<Vec<Option<Sort>>>,
    /// Positions whose term occupies an enclosing position's slot (a rewrite's side in a branch,
    /// an as-pattern's alias in the right branch, the operand of a cast the projection drops):
    /// the enclosing requirement applies to them. Inner pairs come first.
    delegates: Vec<(usize, usize)>,
    /// Whether the terms being visited are still projected. `rewrite_projection` copies the
    /// left side of a rewrite as it is, so inside a left side nothing is projected; it projects
    /// a right side recursively.
    projecting: bool,
    /// Whether the terms being visited are injected as a left-hand side, as `visit_children`
    /// tracks it (sequence items then take `KItem` as their context).
    is_lhs: bool,
}

impl<'a, 'view, 'definition, 't> Walk<'a, 'view, 'definition, 't> {
    fn new(
        injector: &'a SortInjector<'view, 'definition>,
        branch: Branch,
        trie: &'t mut PathTrie,
        projections: &'t Projections,
    ) -> Self {
        Self {
            injector,
            branch,
            trie,
            projections,
            positions: Vec::new(),
            instances: Vec::new(),
            delegates: Vec::new(),
            projecting: branch != Branch::Only,
            is_lhs: branch == Branch::Left,
        }
    }

    /// Visit a child with `(projecting, is_lhs)` set to `mode` for it, restoring them afterwards.
    fn child_with<'r>(
        &mut self,
        mode: (bool, bool),
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
        index: usize,
        hint: &Sort,
    ) -> Result<Slot<'r>, SortInjectionError> {
        let saved = (self.projecting, self.is_lhs);
        (self.projecting, self.is_lhs) = mode;
        let slot = self.child(loaded, resolved, path, index, hint);
        (self.projecting, self.is_lhs) = saved;
        slot
    }

    fn finish(mut self) -> (NodeValues<PositionTyping>, NodeValues<Vec<Option<Sort>>>) {
        for (from, to) in std::mem::take(&mut self.delegates).into_iter().rev() {
            let required = self
                .position(from)
                .and_then(|position| position.required.clone());
            if let Some(position) = self.position_mut(to) {
                position.required = required;
            }
        }
        (self.positions, self.instances)
    }

    fn position(&self, node: usize) -> Option<&PositionTyping> {
        self.positions.get(node).and_then(Option::as_ref)
    }

    fn position_mut(&mut self, node: usize) -> Option<&mut PositionTyping> {
        self.positions.get_mut(node).and_then(Option::as_mut)
    }

    /// Run `work`, an inference of the injector over `term`, with the injector's sort memo
    /// suspended when `term` is a projection built for the walk rather than a node of the
    /// resolved sentence.
    #[expect(
        clippy::ptr_arg,
        reason = "whether the term is borrowed from the sentence decides the memo"
    )]
    fn infer<T>(&self, term: &Cow<'_, Term>, work: impl FnOnce(&Term) -> T) -> T {
        match term {
            Cow::Borrowed(term) => work(term),
            Cow::Owned(term) => self.injector.unmemoized(|| work(term)),
        }
    }

    /// The term compilation sees at a position: `resolved` with the walk's projection applied,
    /// which is `resolved` itself unless a rewrite (or, in the right branch, an as-pattern) lies
    /// within it.
    fn projected<'r>(&self, resolved: &'r Term) -> Cow<'r, Term> {
        let right = self.branch == Branch::Right;
        if self.projecting && self.projections.changes(resolved, right) {
            Cow::Owned(rewrite_projection(resolved, right, &self.injector.subsorts))
        } else {
            Cow::Borrowed(resolved)
        }
    }

    /// Record `required` at `path` and reject the slot's term unless compilation places it there.
    fn place(
        &mut self,
        path: &Cursor,
        slot: &Slot<'_>,
        required: &Sort,
    ) -> Result<(), SortInjectionError> {
        if let Some(position) = self.position_mut(path.node()) {
            position.required = reported(required);
        }
        let Some(sort) = &slot.sort else {
            return Ok(());
        };
        if self.infer(&slot.term, |term| {
            self.injector.places(term, sort, required)
        })? {
            Ok(())
        } else {
            Err(SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
                term: render_term(&slot.term),
                found: sort.clone(),
                required: required.clone(),
            })))
        }
    }

    fn child<'r>(
        &mut self,
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
        index: usize,
        hint: &Sort,
    ) -> Result<Slot<'r>, SortInjectionError> {
        path.push(self.trie, step(index));
        let slot = self.visit(loaded, resolved, path, hint);
        path.pop();
        slot
    }

    fn place_child(
        &mut self,
        path: &mut Cursor,
        index: usize,
        slot: &Slot<'_>,
        required: &Sort,
    ) -> Result<(), SortInjectionError> {
        path.push(self.trie, step(index));
        let placed = self.place(path, slot, required);
        path.pop();
        placed
    }

    fn delegate(&mut self, path: &Cursor, index: usize) {
        let to = self.trie.child(path.node(), step(index));
        self.delegates.push((path.node(), to));
    }

    fn record(&mut self, path: &Cursor, sort: Option<Sort>) {
        let node = path.node();
        if self.positions.len() <= node {
            self.positions.resize_with(node + 1, || None);
        }
        self.positions[node].get_or_insert_default().sort = sort;
    }

    /// Type the loaded term at `path`, whose resolved form (semantic casts replaced by sort
    /// metadata) is `resolved`, at a position of sort `hint`, and every subterm.
    // Invariant: each call records `path` and recurses only into the direct subterms of `loaded` (and the corresponding subterms of `resolved`), extending `path` by one step; the depth of `loaded` bounds the recursion.
    #[expect(
        clippy::wildcard_enum_match_arm,
        reason = "Term is not a sentence kind; only the listed variants are special here"
    )]
    fn visit<'r>(
        &mut self,
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
        hint: &Sort,
    ) -> Result<Slot<'r>, SortInjectionError> {
        self.record(path, None);
        match loaded.unannotated() {
            Term::Apply { label, arguments } if label.semantic_cast_sort().is_some() => {
                let target = label.semantic_cast_sort().expect("a semantic cast");
                let [argument] = arguments.as_slice() else {
                    return Err(SortInjectionError::InvalidArity {
                        label: label.name.clone(),
                        expected: 1,
                        actual: arguments.len(),
                    });
                };
                // Resolution replaced the cast by its operand, which occupies this position.
                let slot = self.child(argument, resolved, path, 0, hint)?;
                let dropped = self.projecting
                    && matches!(
                        (argument.unannotated(), self.branch),
                        (Term::Rewrite { .. }, _) | (Term::As { .. }, Branch::Right)
                    );
                if dropped {
                    // The projection removes the rewrite or as-pattern the cast annotates, and
                    // the cast's own position with it (resolution put a rewrite's cast on each
                    // side, which occupies the cast's position).
                    self.delegate(path, 0);
                } else if let Some(operand) = self.trie.find_child(path.node(), 0)
                    && let Some(position) = self.position_mut(operand)
                {
                    position.required = reported(&target);
                }
                self.record(path, slot.sort.as_ref().and_then(reported));
                Ok(slot)
            }
            Term::Rewrite { left, right } if self.projecting => {
                let (index, side, resolved_side) = match (self.branch, resolved.unannotated()) {
                    (Branch::Left, Term::Rewrite { left: resolved, .. }) => (0, left, resolved),
                    (
                        _,
                        Term::Rewrite {
                            right: resolved, ..
                        },
                    ) => (1, right, resolved),
                    _ => unreachable!("resolution keeps rewrites"),
                };
                // The projection keeps a left side as it is and projects a right side further.
                let projecting = index == 1;
                let is_lhs = self.is_lhs;
                let slot =
                    self.child_with((projecting, is_lhs), side, resolved_side, path, index, hint)?;
                self.delegate(path, index);
                self.record(path, slot.sort.as_ref().and_then(reported));
                Ok(slot)
            }
            Term::As { alias, .. } if self.projecting && self.branch == Branch::Right => {
                let Term::As {
                    alias: resolved_alias,
                    ..
                } = resolved.unannotated()
                else {
                    unreachable!("resolution keeps as-patterns")
                };
                let slot = self.child(alias, resolved_alias, path, 1, hint)?;
                self.delegate(path, 1);
                self.record(path, slot.sort.as_ref().and_then(reported));
                Ok(slot)
            }
            Term::Apply { label, arguments }
                if label.is(InternalLabel::Cells)
                    || label.is(InternalLabel::Dots)
                    || label.is(InternalLabel::NoDots) =>
            {
                let Term::Apply {
                    arguments: resolved_arguments,
                    ..
                } = resolved.unannotated()
                else {
                    unreachable!("resolution keeps applications")
                };
                let k_item = Sort::builtin(BuiltinSort::KItem);
                for (index, (argument, resolved)) in
                    arguments.iter().zip(resolved_arguments).enumerate()
                {
                    self.child(argument, resolved, path, index, &k_item)?;
                }
                Ok(Slot {
                    term: self.projected(resolved),
                    sort: None,
                })
            }
            Term::Apply { label, arguments }
                if self.injector.has_production(loaded, label)
                    && is_authored_cell(self.injector, loaded, label, arguments)? =>
            {
                self.authored_cell(loaded, resolved, path)
            }
            Term::Apply { label, arguments }
                if !self.injector.has_production(loaded, label)
                    && matches!(label.generated(), Some(GeneratedLabel::Projection { .. })) =>
            {
                let Some(GeneratedLabel::Projection { sort_text }) = label.generated() else {
                    unreachable!("matched above")
                };
                let target = parse_sort_text(sort_text)
                    .map_err(|_| SortInjectionError::UnknownLabel(label.name.clone()))?;
                let (
                    Term::Apply {
                        arguments: resolved_arguments,
                        ..
                    },
                    [argument],
                ) = (resolved.unannotated(), arguments.as_slice())
                else {
                    return Err(SortInjectionError::InvalidArity {
                        label: label.name.clone(),
                        expected: 1,
                        actual: arguments.len(),
                    });
                };
                // `project:S` is declared by a later stage as `S ::= "project:S" "(" K ")"`.
                let k = Sort::builtin(BuiltinSort::K);
                let slot = self.child(argument, &resolved_arguments[0], path, 0, &k)?;
                self.place_child(path, 0, &slot, &k)?;
                self.record(path, reported(&target));
                Ok(Slot {
                    term: self.projected(resolved),
                    sort: Some(target),
                })
            }
            _ => self.injected(loaded, resolved, path, hint),
        }
    }

    /// A term the injector types directly: `inject_with_position`'s sort for it at a position of
    /// sort `hint`, and `visit_children`'s placement of its children.
    fn injected<'r>(
        &mut self,
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
        hint: &Sort,
    ) -> Result<Slot<'r>, SortInjectionError> {
        let injector = self.injector;
        let term = self.projected(resolved);
        let sort = self.infer(&term, |term| injector.term_sort(term, Some(hint)))?;
        let (children_of, actual) = (&term, sort.clone());
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "Term is not a sentence kind; only the listed variants are special here"
        )]
        let reported_sort = match term.unannotated() {
            Term::Variable { sort: None, .. } => None,
            _ => reported(&sort),
        };
        self.record(path, reported_sort);
        match (loaded.unannotated(), resolved.unannotated()) {
            (
                Term::Apply { arguments, .. },
                Term::Apply {
                    arguments: resolved_arguments,
                    ..
                },
            ) => {
                let Term::Apply {
                    label,
                    arguments: projected_arguments,
                } = children_of.unannotated()
                else {
                    unreachable!("projection keeps applications")
                };
                let signature = self.infer(children_of, |children_of| {
                    injector.signature(
                        children_of,
                        label,
                        projected_arguments,
                        Some(&actual),
                        false,
                    )
                })?;
                if !signature.label.parameters.is_empty() {
                    set(
                        &mut self.instances,
                        path.node(),
                        signature.label.parameters.iter().map(reported).collect(),
                    );
                }
                for (index, ((argument, resolved), required)) in arguments
                    .iter()
                    .zip(resolved_arguments)
                    .zip(&signature.arguments)
                    .enumerate()
                {
                    let slot = self.child(argument, resolved, path, index, required)?;
                    self.place_child(path, index, &slot, required)?;
                }
            }
            (
                Term::Rewrite { left, right },
                Term::Rewrite {
                    left: resolved_left,
                    right: resolved_right,
                },
            ) => {
                for (index, (side, resolved)) in [(left, resolved_left), (right, resolved_right)]
                    .into_iter()
                    .enumerate()
                {
                    // A rewrite the projection keeps: `visit_children` injects its left side as
                    // a left-hand side and its right side as a right-hand side.
                    let projecting = self.projecting;
                    let slot = self.child_with(
                        (projecting, index == 0),
                        side,
                        resolved,
                        path,
                        index,
                        &actual,
                    )?;
                    self.place_child(path, index, &slot, &actual)?;
                }
            }
            (
                Term::As { pattern, alias },
                Term::As {
                    pattern: resolved_pattern,
                    alias: resolved_alias,
                },
            ) => {
                // Both sides are placed at the as-pattern's sort (a cast on the as-pattern fixes
                // it); a sortless alias takes that sort, a sorted one must fit it.
                let slot = self.child(pattern, resolved_pattern, path, 0, &actual)?;
                self.place_child(path, 0, &slot, &actual)?;
                // The left projection keeps an as-pattern's alias as it is.
                let (projecting, is_lhs) =
                    (self.projecting && self.branch != Branch::Left, self.is_lhs);
                let slot = self.child_with(
                    (projecting, is_lhs),
                    alias,
                    resolved_alias,
                    path,
                    1,
                    &actual,
                )?;
                self.place_child(path, 1, &slot, &actual)?;
            }
            (Term::Sequence(items), Term::Sequence(resolved_items)) => {
                let context = if self.is_lhs {
                    Sort::builtin(BuiltinSort::KItem)
                } else {
                    Sort::builtin(BuiltinSort::K)
                };
                for (index, (item, resolved)) in items.iter().zip(resolved_items).enumerate() {
                    let projected_item = self.projected(resolved);
                    let item_sort = self.infer(&projected_item, |item| {
                        injector.term_sort(item, Some(&context))
                    })?;
                    let required = if item_sort.is_builtin(BuiltinSort::K) {
                        Sort::builtin(BuiltinSort::K)
                    } else {
                        Sort::builtin(BuiltinSort::KItem)
                    };
                    let slot = self.child(item, resolved, path, index, &required)?;
                    self.place_child(path, index, &slot, &required)?;
                }
            }
            _ => {}
        }
        Ok(Slot {
            term,
            sort: Some(sort),
        })
    }

    /// An authored cell `L(#dots|#noDots, body, #dots|#noDots)`: the markers have no sort, and the
    /// body is placed at the cell's single content sort when it has one.
    fn authored_cell<'r>(
        &mut self,
        loaded: &Term,
        resolved: &'r Term,
        path: &mut Cursor,
    ) -> Result<Slot<'r>, SortInjectionError> {
        let injector = self.injector;
        let (
            Term::Apply { label, arguments },
            Term::Apply {
                arguments: resolved_arguments,
                ..
            },
        ) = (loaded.unannotated(), resolved.unannotated())
        else {
            unreachable!("authored cells are applications")
        };
        let Sentence::Production { sort, items, .. } = injector.production(loaded, label)? else {
            unreachable!("the production catalog holds productions")
        };
        #[expect(
            clippy::wildcard_enum_match_arm,
            reason = "ProductionItem is not a sentence kind; only the listed variants are special here"
        )]
        let children = items
            .iter()
            .filter_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        let content = match children.as_slice() {
            [content] => Some(content.clone()),
            _ => None,
        };
        let k_item = Sort::builtin(BuiltinSort::KItem);
        self.child(&arguments[0], &resolved_arguments[0], path, 0, &k_item)?;
        let body_hint = content.clone().unwrap_or_else(|| k_item.clone());
        let body = self.child(&arguments[1], &resolved_arguments[1], path, 1, &body_hint)?;
        if let Some(content) = &content {
            self.place_child(path, 1, &body, content)?;
        }
        self.child(&arguments[2], &resolved_arguments[2], path, 2, &k_item)?;
        self.record(path, reported(sort));
        Ok(Slot {
            term: self.projected(resolved),
            sort: Some(sort.clone()),
        })
    }
}

impl SortInjector<'_, '_> {
    /// Whether injection places a term of sort `actual` at a position of sort `expected`: the
    /// decision `inject_with_position` makes, wrappers included.
    fn places(
        &self,
        term: &Term,
        actual: &Sort,
        expected: &Sort,
    ) -> Result<bool, SortInjectionError> {
        if actual == expected || self.below(actual, expected) {
            return Ok(true);
        }
        Ok(self
            .collection_wrapper(term, actual, expected, term.clone(), false)?
            .is_ok()
            || self
                .user_list_wrapper(actual, expected, term.clone())
                .is_ok())
    }
}

fn step(index: usize) -> u32 {
    u32::try_from(index).expect("a term has fewer than 2^32 children")
}

fn is_authored_cell(
    injector: &SortInjector<'_, '_>,
    term: &Term,
    label: &crate::kast::Label,
    arguments: &[Term],
) -> Result<bool, SortInjectionError> {
    let Sentence::Production { attributes, .. } = injector.production(term, label)? else {
        return Ok(false);
    };
    Ok(attributes.has(AttributeKey::Cell)
        && matches!(arguments, [left, _, right] if is_dots_marker(left) && is_dots_marker(right)))
}

fn is_dots_marker(term: &Term) -> bool {
    matches!(
        term.unannotated(),
        Term::Apply { label, arguments }
            if arguments.is_empty()
                && (label.is(InternalLabel::Dots) || label.is(InternalLabel::NoDots))
    )
}

/// A sort as the view reports it: `None` for a sort that mentions a sort variable, the injector's
/// placeholder for a parameter nothing instantiates.
fn reported(sort: &Sort) -> Option<Sort> {
    fn mentions(sort: &Sort) -> bool {
        sort.is_rigid_variable() || sort.parameters.iter().any(mentions)
    }
    (!mentions(sort)).then(|| sort.clone())
}
