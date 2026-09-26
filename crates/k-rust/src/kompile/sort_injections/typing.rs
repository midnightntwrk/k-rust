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
//! records the node's path in an ordered map, copies or projects the resolved subterm there
//! (`Walk::projected`, linear in the subterm), and asks the injector for the node's sort and
//! placement as injection does. For N nodes of height h that is O(N x h x (log N + P + S)) with
//! the injector's P and S, plus the parametric instance searches and one semantic-cast
//! resolution of the sentence. `kompile.macros.expand` computes this view once per rewrite of a
//! sentence when some macro rule has a parametric head.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use crate::definition::{AttributeKey, PartialOrder, ProductionItem, ResolvedDefinition, Sentence};
use crate::kast::parser::parse_sort_text;
use crate::kast::{FrontendSort, GeneratedLabel, InternalLabel, Sort, Term};
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
    pub positions: BTreeMap<Vec<u32>, PositionTyping>,
    pub branches: BTreeMap<Vec<u32>, BranchTyping>,
    /// The sort of each named variable that semantic-cast resolution determines.
    pub variables: BTreeMap<String, Sort>,
    /// The instance injection gives the label of each application of a parametric production,
    /// one entry per sort parameter (`None` where it leaves the parameter open). It is the
    /// label's own instance, which a downcast placing the application at a narrower sort does
    /// not change. A path typed with different instances in the two branches of a rewrite has
    /// no entry.
    pub(crate) instances: BTreeMap<Vec<u32>, Vec<Option<Sort>>>,
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
/// that resolved and projected term: the sort it places a term at (a downcast's target, an
/// upcast's operand sort), a production's instantiated argument sorts (the selected overload,
/// the joint parametric solver), the least upper bound of a rewrite's branches, the sort of an
/// as-pattern's sides, sequence items at `KItem` or `K`, and conditions at `Bool`. Each term is
/// checked at its position with the injector's decision (one injection, the `K` sequence, the
/// sequence injected above `K`, or a collection or user-list wrapper), so a sentence compilation
/// rejects for an ill-sorted term, an incomparable cast, an ambiguous instantiation, or
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
/// reports its requirement. A cast's operand reports the cast's sort as its requirement; below a
/// downcast the operand's own sort is above it.
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
                used_sort_parameters: RefCell::new(BTreeSet::new()),
            },
            declared,
        })
    }

    pub fn typing(&self, sentence: &Sentence) -> Result<SentenceTyping, SentenceTypingError> {
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
        super::reject_label_parameters(sentence).map_err(|error| SentenceTypingError::Sort {
            location: location.clone(),
            error,
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
        )
        .map_err(|error| SentenceTypingError::Sort { location, error })
    }

    fn typing_of(
        &self,
        loaded: [&Term; 3],
        resolved: [&Term; 3],
        variables: BTreeMap<String, Sort>,
    ) -> Result<SentenceTyping, SortInjectionError> {
        let injector = &self.injector;
        injector.next_sort_parameter.set(0);
        injector.used_sort_parameters.borrow_mut().clear();
        let top = injector.fresh_sort_parameter();
        let boolean = Sort::builtin(BuiltinSort::Bool);

        let mut conditions = Walk::new(injector, Branch::Only);
        for (field, loaded, resolved) in
            [(1u32, loaded[1], resolved[1]), (2, loaded[2], resolved[2])]
        {
            let mut path = vec![field];
            let slot = conditions.visit(loaded, resolved, &mut path, &boolean)?;
            conditions.place(&path, &slot, &boolean)?;
        }
        let (positions, instances) = conditions.finish();
        let mut typing = SentenceTyping {
            positions,
            branches: BTreeMap::new(),
            variables,
            instances,
        };
        // As `inject_rule_body`: a body with a rewrite is the rewrite of its two projections,
        // typed at their least upper bound below a fresh sort variable, and each projection is
        // injected at that bound; a body without one is typed below the fresh variable and
        // injected at its own sort. The body's sort comes from a first walk (the injector's
        // `term_sort` cannot type loaded cell fragments), and the second walk types the body at
        // the position injection places it at.
        let branches: &[Branch] = if has_rewrite(resolved[0]) {
            &[Branch::Left, Branch::Right]
        } else {
            &[Branch::Only]
        };
        let mut sorts = Vec::new();
        for branch in branches {
            let mut walk = Walk::new(injector, *branch);
            sorts.extend(walk.visit(loaded[0], resolved[0], &mut vec![0], &top)?.sort);
        }
        let position = match branches {
            [Branch::Only] => sorts.first().cloned(),
            _ if sorts.is_empty() => None,
            _ => Some(injector.least_upper_bound(&sorts, Some(&top))?),
        };
        let mut maps = Vec::new();
        let mut branch_instances = Vec::new();
        for branch in branches {
            let mut walk = Walk::new(injector, *branch);
            let mut path = vec![0];
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
        let first = maps.remove(0);
        match maps.pop() {
            None => typing.positions.extend(first),
            Some(right) => {
                let mut left = first;
                for (path, right) in right {
                    match left.remove(&path) {
                        Some(left) if left == right => {
                            typing.positions.insert(path, left);
                        }
                        Some(left) => {
                            typing.branches.insert(path, BranchTyping { left, right });
                        }
                        None => {
                            typing.positions.insert(path, right);
                        }
                    }
                }
                typing.positions.extend(left);
            }
        }
        let first = branch_instances.remove(0);
        match branch_instances.pop() {
            None => typing.instances.extend(first),
            Some(right) => {
                let mut left = first;
                for (path, right) in right {
                    match left.remove(&path) {
                        Some(left) if left != right => {}
                        _ => {
                            typing.instances.insert(path, right);
                        }
                    }
                }
                typing.instances.extend(left);
            }
        }
        Ok(typing)
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
struct Slot {
    /// The resolved and projected term at the position.
    term: Term,
    /// The sort injection places it at; `None` for syntax without a sort.
    sort: Option<Sort>,
}

struct Walk<'a, 'view, 'definition> {
    injector: &'a SortInjector<'view, 'definition>,
    branch: Branch,
    positions: BTreeMap<Vec<u32>, PositionTyping>,
    instances: BTreeMap<Vec<u32>, Vec<Option<Sort>>>,
    /// Positions whose term occupies an enclosing position's slot (a rewrite's side in a branch,
    /// an as-pattern's alias in the right branch, the operand of a cast the projection drops):
    /// the enclosing requirement applies to them. Inner pairs come first.
    delegates: Vec<(Vec<u32>, Vec<u32>)>,
    /// Whether the terms being visited are still projected. `rewrite_projection` copies the
    /// left side of a rewrite as it is, so inside a left side nothing is projected; it projects
    /// a right side recursively.
    projecting: bool,
    /// Whether the terms being visited are injected as a left-hand side, as `visit_children`
    /// tracks it (sequence items then take `KItem` as their context).
    is_lhs: bool,
}

impl<'a, 'view, 'definition> Walk<'a, 'view, 'definition> {
    fn new(injector: &'a SortInjector<'view, 'definition>, branch: Branch) -> Self {
        Self {
            injector,
            branch,
            positions: BTreeMap::new(),
            instances: BTreeMap::new(),
            delegates: Vec::new(),
            projecting: branch != Branch::Only,
            is_lhs: branch == Branch::Left,
        }
    }

    /// Visit a child with `(projecting, is_lhs)` set to `mode` for it, restoring them afterwards.
    fn child_with(
        &mut self,
        mode: (bool, bool),
        loaded: &Term,
        resolved: &Term,
        path: &mut Vec<u32>,
        index: usize,
        hint: &Sort,
    ) -> Result<Slot, SortInjectionError> {
        let saved = (self.projecting, self.is_lhs);
        (self.projecting, self.is_lhs) = mode;
        let slot = self.child(loaded, resolved, path, index, hint);
        (self.projecting, self.is_lhs) = saved;
        slot
    }

    #[allow(clippy::type_complexity)]
    fn finish(
        mut self,
    ) -> (
        BTreeMap<Vec<u32>, PositionTyping>,
        BTreeMap<Vec<u32>, Vec<Option<Sort>>>,
    ) {
        for (from, to) in self.delegates.iter().rev() {
            let required = self
                .positions
                .get(from)
                .and_then(|position| position.required.clone());
            if let Some(position) = self.positions.get_mut(to) {
                position.required = required;
            }
        }
        (self.positions, self.instances)
    }

    /// The term compilation sees at a position: `resolved` with the walk's projection applied.
    fn projected(&self, resolved: &Term) -> Term {
        if !self.projecting {
            return resolved.clone();
        }
        let right = self.branch == Branch::Right;
        let mut projects = false;
        resolved.visit_preorder(&mut |term| {
            projects |=
                matches!(term, Term::Rewrite { .. }) || (right && matches!(term, Term::As { .. }));
        });
        if projects {
            rewrite_projection(resolved, right)
        } else {
            resolved.clone()
        }
    }

    /// Record `required` at `path` and reject the slot's term unless compilation places it there.
    fn place(
        &mut self,
        path: &[u32],
        slot: &Slot,
        required: &Sort,
    ) -> Result<(), SortInjectionError> {
        if let Some(position) = self.positions.get_mut(path) {
            position.required = reported(required);
        }
        let Some(sort) = &slot.sort else {
            return Ok(());
        };
        if self.injector.places(&slot.term, sort, required)? {
            Ok(())
        } else {
            Err(SortInjectionError::IllSortedTerm(Box::new(SortMismatch {
                term: render_term(&slot.term),
                found: sort.clone(),
                required: required.clone(),
            })))
        }
    }

    fn child(
        &mut self,
        loaded: &Term,
        resolved: &Term,
        path: &mut Vec<u32>,
        index: usize,
        hint: &Sort,
    ) -> Result<Slot, SortInjectionError> {
        path.push(step(index));
        let slot = self.visit(loaded, resolved, path, hint);
        path.pop();
        slot
    }

    fn place_child(
        &mut self,
        path: &mut Vec<u32>,
        index: usize,
        slot: &Slot,
        required: &Sort,
    ) -> Result<(), SortInjectionError> {
        path.push(step(index));
        let placed = self.place(path, slot, required);
        path.pop();
        placed
    }

    fn delegate(&mut self, path: &[u32], index: usize) {
        let mut to = path.to_vec();
        to.push(step(index));
        self.delegates.push((path.to_vec(), to));
    }

    fn record(&mut self, path: &[u32], sort: Option<Sort>) {
        let position = self.positions.entry(path.to_vec()).or_default();
        position.sort = sort;
    }

    /// Type the loaded term at `path`, whose resolved form (semantic casts replaced by sort
    /// metadata) is `resolved`, at a position of sort `hint`, and every subterm.
    // Invariant: each call records `path` and recurses only into the direct subterms of `loaded` (and the corresponding subterms of `resolved`), extending `path` by one step; the depth of `loaded` bounds the recursion.
    fn visit(
        &mut self,
        loaded: &Term,
        resolved: &Term,
        path: &mut Vec<u32>,
        hint: &Sort,
    ) -> Result<Slot, SortInjectionError> {
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
                    // The projection drops the cast with the rewrite or as-pattern it annotates.
                    self.delegate(path, 0);
                } else {
                    let mut operand = path.clone();
                    operand.push(0);
                    if let Some(position) = self.positions.get_mut(&operand) {
                        position.required = reported(&target);
                    }
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
    fn injected(
        &mut self,
        loaded: &Term,
        resolved: &Term,
        path: &mut Vec<u32>,
        hint: &Sort,
    ) -> Result<Slot, SortInjectionError> {
        let injector = self.injector;
        let term = self.projected(resolved);
        let (sort, downcast) = injector.sort_and_downcast(&term, Some(hint), false)?;
        // A downcast is injected as `project:S` over the term without its cast sort, whose
        // children are then placed by that term's own sort.
        let (children_of, actual) = if downcast.is_some() {
            let mut stripped = term.clone().into_unannotated();
            if let Some(metadata) = term.metadata() {
                let mut metadata = metadata.clone();
                metadata.sort = None;
                stripped = stripped.with_metadata(metadata);
            }
            let natural = injector.term_sort(&stripped, Some(&Sort::builtin(BuiltinSort::K)))?;
            (stripped, natural)
        } else {
            (term.clone(), sort.clone())
        };
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
                let signature = injector.signature(
                    &children_of,
                    label,
                    projected_arguments,
                    Some(&actual),
                    false,
                )?;
                if !signature.label.parameters.is_empty() {
                    self.instances.insert(
                        path.clone(),
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
                    let item_sort =
                        injector.term_sort(&self.projected(resolved), Some(&context))?;
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
    fn authored_cell(
        &mut self,
        loaded: &Term,
        resolved: &Term,
        path: &mut Vec<u32>,
    ) -> Result<Slot, SortInjectionError> {
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
            .is_some()
            || self
                .user_list_wrapper(actual, expected, term.clone())
                .is_some())
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
        sort.name == FrontendSort::SortParam.as_str() || sort.parameters.iter().any(mentions)
    }
    (!mentions(sort)).then(|| sort.clone())
}
