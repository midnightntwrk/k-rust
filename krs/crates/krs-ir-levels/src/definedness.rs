//! Where a partial construct has a value, and the test that states it (NT-37).
//!
//! Some constructs denote a value only on part of their domain:
//!
//! - a sort projection `{t}:>S` (`k::project!(S, t)`), and a collection read KRS projects to a
//!   sort `S` below the `KItem` K's read returns, where `t` (the read) has sort `S`;
//! - a map lookup `m [ k ]`, where `k` is a key of `m`, and a list read `l [ i ]`, where `i` is an
//!   index of `l` (`-size(l) <= i < size(l)`: a negative index counts from the end);
//! - a `let` statement whose pattern may not match its value, where it matches.
//!
//! A sentence's condition holds where it is true. Where a construct it evaluates has no value the
//! condition has none, so it does not hold, and the sentence does not apply. A backend that
//! evaluates the condition reaches the construct before it knows that, and the routes then
//! disagree: Java K's LLVM backend aborts, k-rust leaves the term undefined, and the symbolic
//! backends read `#Bottom`. So the condition states each construct's test before the construct,
//! joined with `andThenBool`, which every route evaluates first: where the test fails the
//! condition is `false`, where it holds the construct has its value, and the condition holds
//! exactly where it held before.
//!
//! The test stands where `false` and "no value" mean the same thing: a conjunct of the
//! condition's top-level conjunction (an operand of `andThenBool` or `andBool` there), or the body
//! of a `#let` that stands there. Below a negation, a disjunction or any other operation, `false`
//! may make the condition hold where the construct has no value, so a construct there is tested
//! at the conjunct that holds it. A conjunct that an earlier conjunct of the same chain already
//! tests needs no test of its own: `k::is!(Int, x) && k::project!(Int, x) > 0` is guarded as
//! written.
//!
//! A pattern that matches evaluated terms (a transition's, a context's, an equation's) evaluates
//! what it computes before the condition, so it holds no partial construct: a lowering that would
//! put one there writes a fresh name the condition equates with the construct's value instead.
//!
//! A result is not tested: where a construct in it has no value, the sentence applies (its
//! pattern matched and its condition held) and its result has no value, which every route ends
//! on; a test would make the sentence not apply there, and another sentence (an `owise` one, a
//! lower priority) apply in its place, which the author did not write.
//!
//! [`unguarded`] is the structural check of that rule over one sentence.

use std::collections::BTreeSet;

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, GeneratedOperation, NodeOrigin, SemanticId,
    SemanticIdKind, SentenceKind,
};

use crate::{
    IrTermKind, ListOperands, MapOperands, RuleBodyRef, SemanticCondition, SemanticRule,
    SemanticSortRef, SemanticTerm,
};

/// The sorts a test reads: the framework's `KItem`, the sort a projected read has when nothing
/// projects it, and the subsort judge a `let` pattern's refutability is read with.
pub struct Sorts<'a> {
    /// The framework's `KItem` sort.
    pub k_item: &'a SemanticSortRef,
    /// Whether a term of the first sort may stand where the second is expected.
    pub is_subsort: &'a dyn Fn(&SemanticSortRef, &SemanticSortRef) -> bool,
}

/// One fact a partial construct needs before it is evaluated.
#[derive(Clone, Copy, Debug)]
pub enum Requirement<'a> {
    /// `isS(t)`: the projection `{t}:>S` has a value. `read` marks a collection read KRS
    /// projects, whose test reads it at `KItem`, the sort K's read has.
    Sort {
        /// The projection's sort.
        sort: &'a SemanticSortRef,
        /// The projected term.
        operand: &'a SemanticTerm,
        /// Whether the operand is a read KRS projects.
        read: bool,
    },
    /// `k in_keys(m)`: the lookup `m [ k ]` has a value.
    Key {
        /// The map.
        map: &'a SemanticTerm,
        /// The key.
        key: &'a SemanticTerm,
    },
    /// `i <Int size(l)`: the read `l [ i ]` is not past the end.
    Below {
        /// The list.
        list: &'a SemanticTerm,
        /// The index.
        index: &'a SemanticTerm,
    },
    /// `0 -Int size(l) <=Int i`: the read `l [ i ]` is not before the start.
    Above {
        /// The list.
        list: &'a SemanticTerm,
        /// The index.
        index: &'a SemanticTerm,
    },
    /// `P' :=K v`: the statement `let P = v;` matches, `P'` being `P` with its names wildcards.
    Match {
        /// The statement's pattern.
        pattern: &'a SemanticTerm,
        /// The statement's value.
        value: &'a SemanticTerm,
    },
}

/// The facts the construct at `term`'s root needs, in the order they must hold; empty for a
/// term that has a value wherever its operands have one. `projected` is false for the operand of
/// a generated sort operation, which the operation reads unprojected.
#[must_use]
pub fn requirements<'a>(
    term: &'a SemanticTerm,
    projected: bool,
    sorts: &Sorts<'_>,
) -> Vec<Requirement<'a>> {
    let read_sort = || {
        (projected && term.sort() != sorts.k_item).then(|| Requirement::Sort {
            sort: term.sort(),
            operand: term,
            read: true,
        })
    };
    match term.kind() {
        IrTermKind::Application {
            application: ApplicationRef::Generated(GeneratedOperation::SortProjection(sort)),
            arguments,
            ..
        } => arguments
            .first()
            .map(|operand| Requirement::Sort {
                sort,
                operand,
                read: false,
            })
            .into_iter()
            .collect(),
        IrTermKind::Map(operands) => match &**operands {
            MapOperands::Get { map, key } => std::iter::once(Requirement::Key { map, key })
                .chain(read_sort())
                .collect(),
            MapOperands::GetOrDefault { .. } => read_sort().into_iter().collect(),
            _ => Vec::new(),
        },
        IrTermKind::List(operands) => match &**operands {
            ListOperands::Get { list, index } => {
                std::iter::once(Requirement::Below { list, index })
                    .chain(
                        (!is_natural_literal(index)).then_some(Requirement::Above { list, index }),
                    )
                    .chain(read_sort())
                    .collect()
            }
            _ => Vec::new(),
        },
        IrTermKind::Let { pattern, value, .. }
            if !irrefutable(pattern, value.sort(), sorts.is_subsort) =>
        {
            vec![Requirement::Match { pattern, value }]
        }
        _ => Vec::new(),
    }
}

/// Whether a `let` pattern matches every value of `value`'s sort: a name of that sort or above.
fn irrefutable(
    pattern: &SemanticTerm,
    value: &SemanticSortRef,
    is_subsort: &dyn Fn(&SemanticSortRef, &SemanticSortRef) -> bool,
) -> bool {
    matches!(pattern.kind(), IrTermKind::Variable { .. }) && is_subsort(value, pattern.sort())
}

/// Whether `index` is an `Int` literal no less than zero, which no list's start is after.
fn is_natural_literal(index: &SemanticTerm) -> bool {
    matches!(index.kind(), IrTermKind::Token { value } if value.bytes().all(|byte| byte.is_ascii_digit()))
        && *index.sort() == SemanticSortRef::Builtin(BuiltinSort::Int)
}

impl<'a> Requirement<'a> {
    /// The construct whose value the requirement states, where a failure is located.
    #[must_use]
    pub const fn subject(&self) -> &'a SemanticTerm {
        match self {
            Self::Sort { operand, .. } => operand,
            Self::Key { key, .. } => key,
            Self::Below { index, .. } | Self::Above { index, .. } => index,
            Self::Match { value, .. } => value,
        }
    }

    /// The terms the test reads, whose names the test needs in scope.
    #[must_use]
    pub fn operands(&self) -> Vec<&'a SemanticTerm> {
        match self {
            Self::Sort { operand, .. } => vec![operand],
            Self::Key { map, key } => vec![map, key],
            Self::Below { list, index } | Self::Above { list, index } => vec![list, index],
            Self::Match { value, .. } => vec![value],
        }
    }

    /// The test: a Bool term that holds exactly where the requirement does. `copy` gives each
    /// copied node of the construct its origin in the test, and `fresh` each node the test adds
    /// (`at` is the node it stands for); `wildcard` names a wildcard of a sort, for a pattern's
    /// names.
    pub fn test(
        &self,
        sorts: &Sorts<'_>,
        copy: &mut dyn FnMut(&NodeOrigin) -> NodeOrigin,
        fresh: &mut dyn FnMut(&NodeOrigin) -> NodeOrigin,
        wildcard: &mut dyn FnMut(&SemanticSortRef) -> SemanticId,
    ) -> SemanticTerm {
        let bool_sort = SemanticSortRef::Builtin(BuiltinSort::Bool);
        let int_sort = SemanticSortRef::Builtin(BuiltinSort::Int);
        let copied = |term: &SemanticTerm, copy: &mut dyn FnMut(&NodeOrigin) -> NodeOrigin| {
            term.map_origins(&mut |origin| copy(origin))
        };
        match *self {
            Self::Sort {
                sort,
                operand,
                read,
            } => {
                let mut tested = copied(operand, copy);
                if read {
                    tested.sort = sorts.k_item.clone();
                }
                SemanticTerm::application(
                    fresh(operand.origin()),
                    bool_sort,
                    ApplicationRef::Generated(GeneratedOperation::SortPredicate(sort.clone())),
                    vec![tested],
                )
            }
            Self::Key { map, key } => SemanticTerm::typed_map(
                fresh(key.origin()),
                bool_sort,
                MapOperands::InKeys {
                    key: copied(key, copy),
                    map: copied(map, copy),
                },
            ),
            Self::Below { list, index } => {
                let size = SemanticTerm::list(
                    fresh(list.origin()),
                    int_sort.clone(),
                    ListOperands::Size {
                        list: copied(list, copy),
                    },
                );
                SemanticTerm::application(
                    fresh(index.origin()),
                    bool_sort,
                    ApplicationRef::Builtin(BuiltinOperation::IntLess),
                    vec![copied(index, copy), size],
                )
            }
            Self::Above { list, index } => {
                let size = SemanticTerm::list(
                    fresh(list.origin()),
                    int_sort.clone(),
                    ListOperands::Size {
                        list: copied(list, copy),
                    },
                );
                let zero = SemanticTerm {
                    origin: fresh(index.origin()),
                    sort: int_sort.clone(),
                    kind: IrTermKind::Token {
                        value: "0".to_owned(),
                    },
                };
                let start = SemanticTerm::application(
                    fresh(list.origin()),
                    int_sort,
                    ApplicationRef::Builtin(BuiltinOperation::IntSub),
                    vec![zero, size],
                );
                SemanticTerm::application(
                    fresh(index.origin()),
                    bool_sort,
                    ApplicationRef::Builtin(BuiltinOperation::IntLessEqual),
                    vec![start, copied(index, copy)],
                )
            }
            Self::Match { pattern, value } => SemanticTerm::matches(
                fresh(value.origin()),
                bool_sort,
                copied(value, copy),
                wildcarded(&copied(pattern, copy), wildcard),
                Vec::new(),
            ),
        }
    }

    /// Whether `fact`, a conjunct that holds where the construct is evaluated, is this
    /// requirement's test.
    #[must_use]
    pub fn holds_by(&self, fact: &SemanticTerm, sorts: &Sorts<'_>) -> bool {
        let test = self.test(
            sorts,
            &mut NodeOrigin::clone,
            &mut NodeOrigin::clone,
            &mut |_| SemanticId::wildcard(0),
        );
        same(fact, &test)
    }
}

/// `pattern` with each name it binds a wildcard of the name's sort.
fn wildcarded(
    pattern: &SemanticTerm,
    wildcard: &mut dyn FnMut(&SemanticSortRef) -> SemanticId,
) -> SemanticTerm {
    let mut term = pattern.clone();
    rename(&mut term, wildcard);
    term
}

fn rename(term: &mut SemanticTerm, wildcard: &mut dyn FnMut(&SemanticSortRef) -> SemanticId) {
    if let IrTermKind::Variable { variable } = &mut term.kind {
        *variable = wildcard(&term.sort);
        return;
    }
    let mut each = |child: &SemanticTerm| {
        let mut child = child.clone();
        rename(&mut child, wildcard);
        Ok::<_, std::convert::Infallible>(child)
    };
    let kind = match &term.kind {
        IrTermKind::Variable { .. } | IrTermKind::Token { .. } => return,
        IrTermKind::Application {
            application,
            arguments,
            instance,
            head_instance_fixed,
        } => IrTermKind::Application {
            application: application.clone(),
            arguments: arguments
                .iter()
                .map(|child| each(child).unwrap_or_else(|never| match never {}))
                .collect(),
            instance: instance.clone(),
            head_instance_fixed: *head_instance_fixed,
        },
        IrTermKind::KSequence { item_sort, items } => IrTermKind::KSequence {
            item_sort: item_sort.clone(),
            items: items
                .iter()
                .map(|child| each(child).unwrap_or_else(|never| match never {}))
                .collect(),
        },
        IrTermKind::Map(operands) => {
            let Ok(operands) = operands.try_map_ref(&mut each);
            IrTermKind::Map(Box::new(operands))
        }
        IrTermKind::List(operands) => {
            let Ok(operands) = operands.try_map_ref(&mut each);
            IrTermKind::List(Box::new(operands))
        }
        IrTermKind::Set(operands) => {
            let Ok(operands) = operands.try_map_ref(&mut each);
            IrTermKind::Set(Box::new(operands))
        }
        IrTermKind::Cell { cell, children } => IrTermKind::Cell {
            cell: cell.clone(),
            children: children
                .iter()
                .map(|child| each(child).unwrap_or_else(|never| match never {}))
                .collect(),
        },
        IrTermKind::Or { alternatives } => {
            let Ok(alternatives) = alternatives.try_map_ref(&mut each);
            IrTermKind::Or { alternatives }
        }
        // A `let` pattern holds no rewrite, alias, test or block.
        IrTermKind::Rewrite { .. }
        | IrTermKind::As { .. }
        | IrTermKind::Matches { .. }
        | IrTermKind::Let { .. } => return,
    };
    term.kind = kind;
}

/// Whether two terms are one term, up to origins and the names of wildcards.
#[must_use]
pub fn same(left: &SemanticTerm, right: &SemanticTerm) -> bool {
    if left.sort() != right.sort() {
        return false;
    }
    let children = |left: &SemanticTerm, right: &SemanticTerm| {
        let (left, right) = (left.children(), right.children());
        left.len() == right.len() && left.iter().zip(&right).all(|(l, r)| same(l, r))
    };
    match (left.kind(), right.kind()) {
        (IrTermKind::Variable { variable: l }, IrTermKind::Variable { variable: r }) => {
            l == r || (is_wildcard(l) && is_wildcard(r))
        }
        (
            IrTermKind::Application {
                application: la,
                instance: li,
                ..
            },
            IrTermKind::Application {
                application: ra,
                instance: ri,
                ..
            },
        ) => la == ra && li == ri && children(left, right),
        (IrTermKind::Token { value: l }, IrTermKind::Token { value: r }) => l == r,
        (IrTermKind::Map(l), IrTermKind::Map(r)) => {
            l.operation() == r.operation() && children(left, right)
        }
        (IrTermKind::List(l), IrTermKind::List(r)) => {
            l.operation() == r.operation() && children(left, right)
        }
        (IrTermKind::Set(l), IrTermKind::Set(r)) => {
            l.operation() == r.operation() && children(left, right)
        }
        (IrTermKind::Cell { cell: l, .. }, IrTermKind::Cell { cell: r, .. }) => {
            l == r && children(left, right)
        }
        (
            IrTermKind::KSequence { item_sort: l, .. },
            IrTermKind::KSequence { item_sort: r, .. },
        ) => l == r && children(left, right),
        (IrTermKind::Rewrite { .. }, IrTermKind::Rewrite { .. })
        | (IrTermKind::Or { .. }, IrTermKind::Or { .. })
        | (IrTermKind::Matches { .. }, IrTermKind::Matches { .. })
        | (IrTermKind::Let { .. }, IrTermKind::Let { .. }) => children(left, right),
        (IrTermKind::As { alias: l, .. }, IrTermKind::As { alias: r, .. }) => {
            l == r && children(left, right)
        }
        _ => false,
    }
}

fn is_wildcard(id: &SemanticId) -> bool {
    id.kind() == SemanticIdKind::Wildcard
}

/// Whether `term` is `andThenBool` or `andBool`, whose operands are the conjuncts of a chain.
#[must_use]
pub fn conjunction(term: &SemanticTerm) -> Option<(&SemanticTerm, &SemanticTerm, bool)> {
    match term.kind() {
        IrTermKind::Application {
            application:
                ApplicationRef::Builtin(
                    operation @ (BuiltinOperation::BoolAndThen | BuiltinOperation::BoolAnd),
                ),
            arguments,
            ..
        } if arguments.len() == 2 => Some((
            &arguments[0],
            &arguments[1],
            *operation == BuiltinOperation::BoolAndThen,
        )),
        _ => None,
    }
}

/// The conjuncts of `term`'s top-level conjunction, which all hold where `term` does.
fn conjuncts<'a>(term: &'a SemanticTerm, output: &mut Vec<&'a SemanticTerm>) {
    match conjunction(term) {
        Some((left, right, _)) => {
            conjuncts(left, output);
            conjuncts(right, output);
        }
        None => output.push(term),
    }
}

/// A partial construct the check found without its test before it.
#[derive(Debug)]
pub struct Unguarded<'a> {
    /// The construct.
    pub construct: &'a SemanticTerm,
    /// Where it stands.
    pub place: Place,
}

/// Where an unguarded construct stands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Place {
    /// In a sentence's condition, with no test before it.
    Condition,
    /// In a pattern that matches evaluated terms, which evaluates it before any condition.
    Pattern,
}

/// The first partial construct `rule` evaluates without its test before it (the module
/// documentation): one in a pattern over evaluated terms, or one in the condition that no
/// earlier conjunct of its chain tests. A result, a claim's start state, and a pattern matched
/// as written (a simplification's, a static clause's) are not read.
#[must_use]
pub fn unguarded<'r>(rule: &'r SemanticRule, sorts: &Sorts<'_>) -> Option<Unguarded<'r>> {
    if matches!(
        rule.kind(),
        SentenceKind::Transition | SentenceKind::Context | SentenceKind::Equation
    ) && rule.simplification().is_none()
    {
        for pattern in pattern_terms(rule) {
            if let Some(construct) = first_partial_in_pattern(pattern, true, sorts) {
                return Some(Unguarded {
                    construct,
                    place: Place::Pattern,
                });
            }
        }
    }
    let Some(SemanticCondition::Bool(condition)) = rule.requires() else {
        return None;
    };
    Checker { sorts }
        .guard_point(condition.term(), &[], &BTreeSet::new())
        .map(|construct| Unguarded {
            construct,
            place: Place::Condition,
        })
}

/// The terms of `rule` that are matched: a term rewrite's left side (with its rewrites' right
/// sides, which are built, read by [`first_partial_in_pattern`]), each matched cell's pattern.
fn pattern_terms(rule: &SemanticRule) -> Vec<&SemanticTerm> {
    match rule.relational_body() {
        RuleBodyRef::Term(body) => vec![body.local_term().unwrap_or_else(|| body.from())],
        RuleBodyRef::Configuration { body, .. } => body
            .parts()
            .iter()
            .filter_map(krs_ir::ClausePart::pre_term)
            .collect(),
        RuleBodyRef::Predicate(_) => Vec::new(),
    }
}

/// Whether `term` evaluates a partial construct anywhere, its rewrites' left sides included;
/// `projected` is false for the operand of a generated sort operation.
#[must_use]
pub fn holds_partial(term: &SemanticTerm, projected: bool, sorts: &Sorts<'_>) -> bool {
    first_partial_in_pattern(term, projected, sorts).is_some()
}

fn first_partial_in_pattern<'a>(
    term: &'a SemanticTerm,
    projected: bool,
    sorts: &Sorts<'_>,
) -> Option<&'a SemanticTerm> {
    if let IrTermKind::Rewrite { from, .. } = term.kind() {
        return first_partial_in_pattern(from, projected, sorts);
    }
    if !requirements(term, projected, sorts).is_empty() {
        return Some(term);
    }
    let generated = is_generated(term);
    term.children()
        .into_iter()
        .find_map(|child| first_partial_in_pattern(child, !generated, sorts))
}

/// Whether `term` applies a generated sort operation, which reads its operand unprojected.
fn is_generated(term: &SemanticTerm) -> bool {
    matches!(
        term.kind(),
        IrTermKind::Application {
            application: ApplicationRef::Generated(_),
            ..
        }
    )
}

/// The check of one condition.
struct Checker<'s, 'a> {
    sorts: &'s Sorts<'a>,
}

impl Checker<'_, '_> {
    /// The first construct of `term`, a Bool at a place where `false` means "does not hold", that
    /// `established` (the earlier conjuncts of its chain) does not test. `locals` are the names
    /// the `#let`s around `term` bind.
    fn guard_point<'t>(
        &self,
        term: &'t SemanticTerm,
        established: &[&'t SemanticTerm],
        locals: &BTreeSet<SemanticId>,
    ) -> Option<&'t SemanticTerm> {
        if let Some((left, right, ordered)) = conjunction(term) {
            if let Some(found) = self.guard_point(left, established, locals) {
                return Some(found);
            }
            let mut after = established.to_vec();
            if ordered {
                conjuncts(left, &mut after);
            }
            return self.guard_point(right, &after, locals);
        }
        if let IrTermKind::Let {
            pattern,
            value,
            body,
            binds,
        } = term.kind()
            && *body.sort() == SemanticSortRef::Builtin(BuiltinSort::Bool)
        {
            if let Some(found) = self.leaf(value, true, established, &BTreeSet::new()) {
                return Some(found);
            }
            let statement = requirements(term, true, self.sorts);
            if statement
                .iter()
                .any(|requirement| !self.established(requirement, established))
            {
                return Some(value);
            }
            let _ = pattern;
            let mut inner = locals.clone();
            inner.extend(binds.iter().cloned());
            return self.guard_point(body, established, &inner);
        }
        self.leaf(term, true, established, &BTreeSet::new())
    }

    /// The first construct in `term` (no place of which is a guard point) whose requirements
    /// `established` does not all hold; `bound` are the names the `#let`s inside the leaf around
    /// `term` bind, which no test at the guard point can read.
    fn leaf<'t>(
        &self,
        term: &'t SemanticTerm,
        projected: bool,
        established: &[&'t SemanticTerm],
        bound: &BTreeSet<SemanticId>,
    ) -> Option<&'t SemanticTerm> {
        let generated = is_generated(term);
        let mut inner = bound.clone();
        if let IrTermKind::Let {
            value, body, binds, ..
        } = term.kind()
        {
            if let Some(found) = self.leaf(value, true, established, bound) {
                return Some(found);
            }
            inner.extend(binds.iter().cloned());
            if let Some(found) = self.leaf(body, true, established, &inner) {
                return Some(found);
            }
        } else if let IrTermKind::Matches { subject, .. } = term.kind() {
            if let Some(found) = self.leaf(subject, true, established, bound) {
                return Some(found);
            }
        } else {
            for child in term.children() {
                if let Some(found) = self.leaf(child, !generated, established, bound) {
                    return Some(found);
                }
            }
        }
        let requirements = requirements(term, projected, self.sorts);
        requirements
            .iter()
            .any(|requirement| {
                reads_any(requirement, bound) || !self.established(requirement, established)
            })
            .then_some(term)
    }

    fn established(&self, requirement: &Requirement<'_>, established: &[&SemanticTerm]) -> bool {
        established
            .iter()
            .any(|fact| requirement.holds_by(fact, self.sorts))
    }
}

/// Whether the requirement's test reads a name in `names`.
#[must_use]
pub fn reads_any(requirement: &Requirement<'_>, names: &BTreeSet<SemanticId>) -> bool {
    !names.is_empty()
        && requirement
            .operands()
            .into_iter()
            .any(|operand| reads(operand, names))
}

fn reads(term: &SemanticTerm, names: &BTreeSet<SemanticId>) -> bool {
    match term.kind() {
        IrTermKind::Variable { variable } => names.contains(variable),
        _ => term.children().into_iter().any(|child| reads(child, names)),
    }
}

#[cfg(test)]
mod tests {
    use krs_ir::testing::{item, item_in, origin, package_with};
    use krs_ir::{ApplicationRef, BuiltinOperation, ItemKind, SemanticId, SentenceKind};

    use super::{Place, Sorts, unguarded};
    use crate::{
        MapOperands, SemanticCondition, SemanticRule, SemanticRuleCondition, SemanticSortRef,
        SemanticTerm, SemanticVariable,
    };

    fn k_item() -> SemanticSortRef {
        SemanticSortRef::declared(item_in(
            package_with("KRS-FRAMEWORK", "krs", "0.1.0", "framework"),
            "syntax",
            "KItem",
            ItemKind::Sort,
        ))
    }

    fn int() -> SemanticSortRef {
        SemanticSortRef::Builtin(krs_ir::BuiltinSort::Int)
    }

    fn bool_sort() -> SemanticSortRef {
        SemanticSortRef::Builtin(krs_ir::BuiltinSort::Bool)
    }

    fn x(key: &str) -> SemanticTerm {
        SemanticTerm::variable(origin(key), k_item(), SemanticId::new("X").unwrap())
    }

    fn generated(
        key: &str,
        operation: krs_ir::GeneratedOperation<SemanticSortRef>,
        sort: SemanticSortRef,
        operand: SemanticTerm,
    ) -> SemanticTerm {
        SemanticTerm::application(
            origin(key),
            sort,
            ApplicationRef::Generated(operation),
            vec![operand],
        )
    }

    fn builtin(
        key: &str,
        operation: BuiltinOperation,
        sort: SemanticSortRef,
        arguments: Vec<SemanticTerm>,
    ) -> SemanticTerm {
        SemanticTerm::application(
            origin(key),
            sort,
            ApplicationRef::Builtin(operation),
            arguments,
        )
    }

    /// `{X}:>Int >Int 0`.
    fn positive(key: &str) -> SemanticTerm {
        let zero = SemanticTerm::token(origin(&format!("{key}.zero")), int(), "0").unwrap();
        let projected = generated(
            &format!("{key}.projection"),
            krs_ir::GeneratedOperation::SortProjection(int()),
            int(),
            x(&format!("{key}.x")),
        );
        builtin(
            key,
            BuiltinOperation::IntGreater,
            bool_sort(),
            vec![projected, zero],
        )
    }

    fn is_int(key: &str) -> SemanticTerm {
        generated(
            key,
            krs_ir::GeneratedOperation::SortPredicate(int()),
            bool_sort(),
            x(&format!("{key}.x")),
        )
    }

    fn and_then(key: &str, left: SemanticTerm, right: SemanticTerm) -> SemanticTerm {
        builtin(
            key,
            BuiltinOperation::BoolAndThen,
            bool_sort(),
            vec![left, right],
        )
    }

    /// The transition `X => X` with condition `requires`, or `from => X` when `from` is given.
    fn rule(requires: Option<SemanticTerm>, from: Option<SemanticTerm>) -> SemanticRule {
        let rewrite = SemanticTerm::rewrite(
            origin("rule.rewrite"),
            k_item(),
            from.unwrap_or_else(|| x("rule.from")),
            x("rule.to"),
        )
        .unwrap();
        SemanticRule::new(
            origin("rule"),
            item("rules", "r", ItemKind::Rule),
            SentenceKind::Transition,
            vec![SemanticVariable::new(
                SemanticId::new("X").unwrap(),
                k_item(),
            )],
            rewrite,
        )
        .unwrap()
        .with_requires(requires.map(|term| {
            SemanticCondition::Bool(SemanticRuleCondition::new(origin("rule.requires"), term))
        }))
        .unwrap()
    }

    fn check(rule: &SemanticRule) -> Option<Place> {
        let k_item = k_item();
        let is_subsort = |candidate: &SemanticSortRef, expected: &SemanticSortRef| {
            candidate == expected || *expected == k_item
        };
        let sorts = Sorts {
            k_item: &k_item,
            is_subsort: &is_subsort,
        };
        unguarded(rule, &sorts).map(|found| found.place)
    }

    #[test]
    fn a_projection_in_a_condition_needs_its_test_before_it_at_a_conjunct() {
        assert_eq!(
            check(&rule(Some(positive("c")), None)),
            Some(Place::Condition)
        );
        let guarded = and_then("c", is_int("c.test"), positive("c.right"));
        assert_eq!(check(&rule(Some(guarded), None)), None);
        // After the construct, the test comes too late.
        let late = and_then("c", positive("c.left"), is_int("c.test"));
        assert_eq!(check(&rule(Some(late), None)), Some(Place::Condition));
        // Below a negation `false` makes the condition hold: the test there guards nothing.
        let negated = builtin(
            "c",
            BuiltinOperation::BoolNot,
            bool_sort(),
            vec![and_then("c.inner", is_int("c.test"), positive("c.right"))],
        );
        assert_eq!(check(&rule(Some(negated), None)), Some(Place::Condition));
    }

    #[test]
    fn a_lookup_needs_its_key_and_its_projection_their_sort() {
        let map = || {
            SemanticTerm::typed_map(
                origin("m"),
                crate::IrSortRef::Builtin(krs_ir::BuiltinSort::Map),
                MapOperands::Empty,
            )
        };
        let read = |key: &str, sort: SemanticSortRef| {
            SemanticTerm::typed_map(
                origin(key),
                sort,
                MapOperands::Get {
                    map: map().with_origin(origin(&format!("{key}.map"))),
                    key: x(&format!("{key}.key")),
                },
            )
        };
        assert_eq!(
            check(&rule(Some(read("c", bool_sort())), None)),
            Some(Place::Condition)
        );
        let in_keys = SemanticTerm::typed_map(
            origin("c.in-keys"),
            bool_sort(),
            MapOperands::InKeys {
                key: x("c.in-keys.key"),
                map: map().with_origin(origin("c.in-keys.map")),
            },
        );
        let is_bool = generated(
            "c.is-bool",
            krs_ir::GeneratedOperation::SortPredicate(bool_sort()),
            bool_sort(),
            read("c.is-bool.read", k_item()),
        );
        let guarded = and_then(
            "c",
            in_keys.clone(),
            and_then("c.rest", is_bool, read("c.read", bool_sort())),
        );
        assert_eq!(check(&rule(Some(guarded), None)), None);
        // The key alone leaves the projection to `Bool` untested.
        let half = and_then("c", in_keys, read("c.read", bool_sort()));
        assert_eq!(check(&rule(Some(half), None)), Some(Place::Condition));
        // A pattern over evaluated terms evaluates the lookup before any condition.
        let wrapped = builtin(
            "p",
            BuiltinOperation::KEqualEq,
            bool_sort(),
            vec![read("p.read", k_item()), x("p.x")],
        );
        assert_eq!(check(&rule(None, Some(wrapped))), Some(Place::Pattern));
    }
}
