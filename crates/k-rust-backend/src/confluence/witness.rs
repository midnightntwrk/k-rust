//! Witness equations: the equations `W` that interpret a stuck partial application at an element
//! no normal form of the definition denotes, so that every pair is read in one model with
//! nonempty carriers, `M+` (`docs/compatibility.md`, "Anywhere rules").
//!
//! `M+` is the normal forms of innermost evaluation by `R ∪ W` over the signature with one fresh
//! free constant `*_S` for each sort `S` outside `Sorts::surely_inhabited` (with every instance of
//! a parametric sort that is neither hooked nor a collection). A witness `p => t` is
//! well formed when:
//!
//! - `p` applies a declared partial function that is not overloaded and has no hook to
//!   constructor, injection and variable terms, and holds a variable whose sort has no normal form
//!   (`Context::empty_sort`);
//! - `t` is built from constructors, injections and `p`'s variables, and `sort(t) <= sort(p)`;
//!
//! so it raises no precondition row, and no instance of `p` free of `*` exists (a normal form of a
//! sort with no normal form over the signature holds `*`): `M+` agrees with `M_NF` on every term
//! free of `*`. The witnesses of one index form one group below every group of that index
//! ([`WITNESS_PRIORITY`]).
//!
//! The check finds them in two passes (`check_detached`):
//!
//! - **proposal** (pass 1, a heuristic): an overlap over a sort with no normal form that does not
//!   join, in a pair the load's relevance filter classifies, is joined again in open mode
//!   (`join::Mode::Open`), which reads a stuck partial application holding a variable of such a
//!   sort as a settled atom. Where the two reached sides differ only at such an atom `p` on one
//!   side and `inj{S1,T}(u)` on the other ([`differences`]), with `S1 <= sort(p)` and
//!   `vars(u) ⊆ vars(p)`, `p => inj{S1,sort(p)}(u)` is proposed. A proposal whose left-hand side
//!   unifies with another's of the same root while their right-hand sides differ at the unifier
//!   is dropped, and
//!   the others are ordered by index, then by text ([`settle`]);
//! - **validation** (pass 2): the whole check again on `R ∪ W`, which still reads a stuck partial
//!   application as `\bottom` (true in `M+`, where `W` is offered too);
//! - **adoption** ([`adopted`]), decided once, by the full check (`CheckScope::All`): pass 2 is
//!   used when (1) every proposing pair and every pair with a witness joins, (2) nothing pass 1
//!   joined or refuted is lost, (3) fewer pairs do not join, and (4) no witness head is tainted
//!   in pass 2's closure (unfiltered). Otherwise pass 1 is kept, with `W` empty. The load's scope
//!   checks condition 4 again on its own pass 2 ([`heads_untainted`]) and keeps its pass 1 when a
//!   witness head is tainted there. One round.

use std::{collections::BTreeSet, sync::Arc};

use k_rust_kore::kore::printer::Printer;

use super::{Checked, Context, UnjoinedPair, symbols::Class};
use crate::{
    externalize,
    rule::{
        Concreteness, RewriteRule, RuleAttributes, RuleOrigin, RuleRhs, make_rule, rename_apart,
        term_index,
    },
    substitution::{Substitution, substitute},
    term::{HeadRole, Name, Term, TermKind},
};

/// The priority of every witness group: below every priority group a definition can write
/// (`owise` is 200). A witness at an index that already has a group at this priority, or whose
/// bare-variable index has one, is not proposed, since it would not be below that group.
pub(super) const WITNESS_PRIORITY: u8 = u8::MAX;

/// A pair, by what identifies it in both passes: the unique ids of its two equations (a hook
/// pair's second is a written meaning, labelled `{hook} meaning {i}`), the position, whether it
/// is a hook pair, and whether it is a report on one equation.
pub(super) type PairKey = (String, String, Vec<usize>, bool, bool);

/// The key of a pair of the verdict.
pub(super) fn pair_key(pair: &UnjoinedPair) -> PairKey {
    (
        pair.first.attributes.unique_id.clone(),
        pair.second.attributes.unique_id.clone(),
        pair.position.clone(),
        pair.hook.is_some(),
        pair.reason.describes_one_equation(),
    )
}

/// One witness equation pass 1 proposes, with the pair that proposed it.
pub(super) struct Proposal {
    pub(super) lhs: Term,
    pub(super) rhs: Term,
    pub(super) pair: PairKey,
    /// The origins of the proposing pair's first equation, which the witness is reported with.
    pub(super) origins: Vec<RuleOrigin>,
}

/// The witnesses of pass 1, settled ([`settle`]), with the pairs that proposed them.
#[derive(Default)]
pub(super) struct Witnesses {
    /// The proposals pass 1 made, before they were settled.
    pub(super) proposed: usize,
    /// The witness equations, in their order.
    pub(super) rules: Vec<Arc<RewriteRule>>,
    /// The pairs whose proposal is among `rules`.
    pub(super) proposing: BTreeSet<PairKey>,
}

/// Whether `term` is built from free-constructor applications, injections and variables.
fn constructed(term: &Term) -> bool {
    match term.kind() {
        TermKind::Variable(_) => true,
        TermKind::Injection { term, .. } => constructed(term),
        TermKind::Application {
            symbol, arguments, ..
        } => {
            symbol.attributes.head_role() == HeadRole::FreeConstructor
                && arguments.iter().all(constructed)
        }
        TermKind::DomainValue { .. }
        | TermKind::Map { .. }
        | TermKind::List { .. }
        | TermKind::Set { .. }
        | TermKind::And(..) => false,
    }
}

/// `term` with its nested injections composed: the source sort of the outermost injection chain
/// and the term inside it (`term` itself, at its own sort, when it is no injection).
fn strip(term: &Term) -> (crate::term::Sort, Term) {
    match term.kind() {
        TermKind::Injection { source, term, .. } => match term.kind() {
            TermKind::Injection { .. } => strip(term),
            _ => (*source, term.clone()),
        },
        _ => (term.sort(), term.clone()),
    }
}

/// Whether `p` may head a witness: it is one of the join's open atoms, applies a declared
/// partial function that is not overloaded and has no hook (which the open atoms already are),
/// to constructor, injection and variable terms.
fn witness_head(context: &Context<'_>, p: &Term, open_atoms: &[Term]) -> bool {
    let TermKind::Application {
        symbol, arguments, ..
    } = p.kind()
    else {
        return false;
    };
    open_atoms.contains(p)
        && Class::of(symbol) == Class::PartialFunction
        && symbol.attributes.hook.is_none()
        && !context.definition.overloads().is_overloaded(&symbol.name)
        && arguments.iter().all(constructed)
        && context.holds_empty_variable(p)
}

/// The witness equations that make `reached`, the two sides an open-mode join reached, equal:
/// `None` when they differ anywhere but at open atoms the design's shape can fill (module
/// documentation). The sides are walked together: equal subterms need nothing, two applications
/// of one symbol are compared argument by argument, and where the two differ, one side's
/// injection chain must end in an open atom `p` whose sort the other side's source sort is below.
pub(super) fn differences(
    context: &Context<'_>,
    reached: &(Option<Term>, Option<Term>),
    open_atoms: &[Term],
) -> Option<Vec<(Term, Term)>> {
    let (Some(left), Some(right)) = reached else {
        return None;
    };
    let mut found = Vec::new();
    walk(context, left, right, open_atoms, &mut found).then_some(found)
}

fn walk(
    context: &Context<'_>,
    left: &Term,
    right: &Term,
    open_atoms: &[Term],
    found: &mut Vec<(Term, Term)>,
) -> bool {
    if left == right {
        return true;
    }
    let ((left_sort, left_inner), (right_sort, right_inner)) = (strip(left), strip(right));
    if left_sort == right_sort
        && let (
            TermKind::Application {
                symbol: left_symbol,
                sort_arguments: left_sorts,
                arguments: left_arguments,
            },
            TermKind::Application {
                symbol: right_symbol,
                sort_arguments: right_sorts,
                arguments: right_arguments,
            },
        ) = (left_inner.kind(), right_inner.kind())
        && left_symbol.name == right_symbol.name
        && left_sorts == right_sorts
        && left_arguments.len() == right_arguments.len()
        && !open_atoms.contains(&left_inner)
        && !open_atoms.contains(&right_inner)
    {
        return left_arguments
            .iter()
            .zip(right_arguments)
            .all(|(left, right)| walk(context, left, right, open_atoms, found));
    }
    for ((atom_sort, atom), (value_sort, value)) in [
        ((right_sort, &right_inner), (left_sort, &left_inner)),
        ((left_sort, &left_inner), (right_sort, &right_inner)),
    ] {
        if !witness_head(context, atom, open_atoms) || !constructed(value) {
            continue;
        }
        if !value
            .attributes()
            .variables
            .iter()
            .all(|variable| atom.attributes().variables.contains(variable))
        {
            continue;
        }
        if !matches!(
            context
                .definition
                .sort_graph()
                .check_subsort(&value_sort, &atom_sort),
            Ok(true)
        ) {
            continue;
        }
        let rhs = if value_sort == atom_sort {
            value.clone()
        } else {
            Term::injection(value_sort, atom_sort, value.clone())
        };
        found.push((atom.clone(), rhs));
        return true;
    }
    false
}

/// `lhs => rhs` with its variables renamed to `VarWitness{i}` in order of first occurrence in
/// `lhs` (every variable of `rhs` is one of `lhs`'s), so that two proposals equal up to a renaming
/// are one, and the order and the text of the witnesses depend on nothing a pair's variables were
/// renamed apart with.
fn canonical(lhs: &Term, rhs: &Term) -> (Term, Term) {
    let mut seen = rustc_hash::FxHashSet::default();
    let mut order = Vec::new();
    super::memo::first_occurrences(lhs, &mut seen, &mut order);
    let renaming = order
        .into_iter()
        .enumerate()
        .map(|(counter, variable)| {
            let renamed = Term::variable(variable.with_name(format!("VarWitness{counter}")));
            (variable, renamed)
        })
        .collect::<Substitution>();
    (substitute(lhs, &renaming), substitute(rhs, &renaming))
}

fn text(term: &Term) -> String {
    Printer::compact().print_pattern(&externalize::term(term))
}

/// Settle pass 1's `proposals` into the witnesses pass 2 reads: each renamed canonically, equal
/// ones merged; a proposal whose left-hand side unifies with another's of the same root while
/// their right-hand sides differ at a unifier (or whose unification is undecided) dropped with
/// that other; one at an index with a group at [`WITNESS_PRIORITY`] dropped; the rest ordered by
/// index, then by text, each made an executable equation of that priority.
pub(super) fn settle(context: &mut Context<'_>, proposals: Vec<Proposal>) -> Witnesses {
    let proposed = proposals.len();
    // Canonical proposals, merged, each with its proposing pairs and origins.
    let mut merged: Vec<(Term, Term, BTreeSet<PairKey>, Vec<RuleOrigin>)> = Vec::new();
    for proposal in proposals {
        let (lhs, rhs) = canonical(&proposal.lhs, &proposal.rhs);
        if let Some(existing) = merged
            .iter_mut()
            .find(|(left, right, ..)| *left == lhs && *right == rhs)
        {
            existing.2.insert(proposal.pair);
            continue;
        }
        merged.push((lhs, rhs, BTreeSet::from([proposal.pair]), proposal.origins));
    }
    let rules = merged
        .iter()
        .map(|(lhs, rhs, _, origins)| witness_rule(lhs, rhs, origins.clone()))
        .collect::<Vec<_>>();
    let mut dropped = vec![false; rules.len()];
    let nothing_normal = |_: &Term| false;
    for (first, left) in rules.iter().enumerate() {
        for (offset, right) in rules[first + 1..].iter().enumerate() {
            let second = first + 1 + offset;
            // Two left-hand sides with different roots never match one redex, so they cannot
            // conflict; asking the unifier would read their two function roots as undecided.
            if term_index(&left.lhs) != term_index(&right.lhs) {
                continue;
            }
            let right = rename_apart(right, &left.computed_attributes.variables, &[])
                .map_or_else(|| right.as_ref().clone(), |(renamed, _)| renamed);
            let (RuleRhs::Term(left_rhs), RuleRhs::Term(right_rhs)) = (&left.rhs, &right.rhs)
            else {
                unreachable!("a witness has a term right-hand side");
            };
            let conflict = match context.unify(true, &nothing_normal, &left.lhs, &right.lhs) {
                Ok(unifiers) => unifiers
                    .iter()
                    .any(|unifier| substitute(left_rhs, unifier) != substitute(right_rhs, unifier)),
                Err(_) => true,
            };
            if conflict && !super::switches::active().adopt_unvalidated_witnesses {
                dropped[first] = true;
                dropped[second] = true;
            }
        }
    }
    let occupied = |index: &crate::rule::TermIndex| {
        [index.clone(), crate::rule::TermIndex::Variable]
            .iter()
            .any(|index| {
                context
                    .groups
                    .get(index)
                    .is_some_and(|groups| groups.contains_key(&WITNESS_PRIORITY))
            })
    };
    let mut kept = merged
        .into_iter()
        .zip(rules)
        .zip(dropped)
        .filter(|((_, rule), dropped)| !dropped && !occupied(&term_index(&rule.lhs)))
        .map(|((merged, rule), _)| {
            let key = (term_index(&rule.lhs), text(&merged.0), text(&merged.1));
            (key, merged.2, rule)
        })
        .collect::<Vec<_>>();
    kept.sort_by(|(left, ..), (right, ..)| left.cmp(right));
    let mut witnesses = Witnesses {
        proposed,
        ..Witnesses::default()
    };
    for (_, pairs, rule) in kept {
        witnesses.proposing.extend(pairs);
        witnesses.rules.push(rule);
    }
    witnesses
}

/// The executable equation `lhs => rhs` of [`WITNESS_PRIORITY`], labelled by its text.
fn witness_rule(lhs: &Term, rhs: &Term, origins: Vec<RuleOrigin>) -> Arc<RewriteRule> {
    let attributes = RuleAttributes {
        priority: WITNESS_PRIORITY,
        label: None,
        unique_id: format!("witness {} => {}", text(lhs), text(rhs)),
        simplification: false,
        preserves_definedness: false,
        concreteness: Concreteness::Unconstrained,
        smt_lemma: false,
        executable: true,
        origins,
        overload: None,
    };
    Arc::new(make_rule(
        lhs.clone(),
        RuleRhs::Term(rhs.clone()),
        Vec::new(),
        Vec::new(),
        attributes,
        BTreeSet::new(),
        None,
    ))
}

/// The root symbol of a witness's left-hand side.
pub(super) fn head(rule: &RewriteRule) -> Option<Name> {
    match rule.lhs.kind() {
        TermKind::Application { symbol, .. } => Some(symbol.name.clone()),
        _ => None,
    }
}

/// Whether the full check's pass 2 (`second`, on `R ∪ W`) is adopted over its pass 1 (`first`):
/// conditions 1-4 of the module documentation.
pub(super) fn adopted(first: &Checked, second: &Checked, witnesses: &Witnesses) -> bool {
    let before = first.unjoined.iter().map(pair_key).collect::<BTreeSet<_>>();
    let after = second
        .unjoined
        .iter()
        .map(pair_key)
        .collect::<BTreeSet<_>>();
    let ids = witnesses
        .rules
        .iter()
        .map(|rule| rule.attributes.unique_id.as_str())
        .collect::<BTreeSet<_>>();
    // (1) Every proposing pair, and every pair with a witness, joins.
    let proposing_join = witnesses.proposing.iter().all(|key| !after.contains(key));
    let witness_pairs_join = second.unjoined.iter().all(|pair| {
        !ids.contains(pair.first.attributes.unique_id.as_str())
            && !ids.contains(pair.second.attributes.unique_id.as_str())
    });
    // (2) Nothing pass 1 joined or refuted is lost, and no precondition row is added.
    let rows = |checked: &Checked| {
        checked
            .violations
            .iter()
            .map(|violation| {
                (
                    violation
                        .rule
                        .as_ref()
                        .map(|rule| rule.attributes.unique_id.clone()),
                    violation.kind.to_string(),
                )
            })
            .collect::<BTreeSet<_>>()
    };
    let nothing_lost = after.is_subset(&before) && rows(second).is_subset(&rows(first));
    // (3) Fewer pairs do not join.
    let fewer = second.unjoined.len() < first.unjoined.len();
    // (4) No witness head is tainted in the unfiltered closure.
    proposing_join
        && witness_pairs_join
        && nothing_lost
        && fewer
        && heads_untainted(second, &witnesses.rules)
}

/// Condition 4 on a pass with the witnesses `rules`: no witness head is in its unfiltered
/// closure (`Checked::tainted_symbols`). Checked on the full check's second pass, and again on the
/// load's own, whose closure the full check's contains only where the two scopes classify alike.
/// A witness pair the pass leaves unjoined seeds the witness, whose head T1 then taints, so this
/// also refuses such a pass. Test switch `adopt_with_tainted_witness_head` drops condition 4 in
/// both places, and so does `witnesses_only_at_their_pair`: the pass it validates keeps every
/// pair but the proposing ones at its pass-1 classification ([`only_at_their_pairs`]), so its
/// closure is not the one `pass` read, where a pair over a sort with no normal form that the
/// witnesses split seeds like any other.
pub(super) fn heads_untainted(pass: &Checked, rules: &[Arc<RewriteRule>]) -> bool {
    let switches = super::switches::active();
    switches.adopt_with_tainted_witness_head
        || switches.witnesses_only_at_their_pair
        || rules
            .iter()
            .filter_map(|rule| head(rule))
            .all(|head| !pass.tainted_symbols.contains(&head))
}

/// Test switch `adopt_unvalidated_witnesses`: `first`, pass 1's verdict, with every pair that
/// proposed one of `witnesses` read as joined by its own proposal and `witnesses` adopted, no
/// pass 2 run.
pub(super) fn adopted_unvalidated(mut first: Checked, witnesses: &Witnesses) -> Checked {
    first
        .unjoined
        .retain(|pair| !witnesses.proposing.contains(&pair_key(pair)));
    first.counts.unjoined = first.unjoined.len();
    first.counts.witnesses = witnesses.rules.len();
    first.witnesses.clone_from(&witnesses.rules);
    first
}

/// Test switch `witnesses_only_at_their_pair`: `second`, a pass 2 verdict, with the witnesses
/// validated only at their proposing pairs: every other pair it lists is replaced by what `first`,
/// the same scope's pass 1, lists.
pub(super) fn only_at_their_pairs(
    second: &mut Checked,
    first: &Checked,
    proposing: &BTreeSet<PairKey>,
) {
    if !super::switches::active().witnesses_only_at_their_pair {
        return;
    }
    second
        .unjoined
        .retain(|pair| proposing.contains(&pair_key(pair)));
    second.unjoined.extend(
        first
            .unjoined
            .iter()
            .filter(|pair| !proposing.contains(&pair_key(pair)))
            .cloned(),
    );
    second.counts.unjoined = second.unjoined.len();
}

/// Test builds: the canonical text of a witness, `lhs => rhs`.
#[cfg(test)]
pub(crate) fn witness_text(rule: &RewriteRule) -> String {
    let RuleRhs::Term(rhs) = &rule.rhs else {
        unreachable!("a witness has a term right-hand side");
    };
    format!("{} => {}", text(&rule.lhs), text(rhs))
}
