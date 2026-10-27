//! Request-local candidates from existing source observation views.
//!
//! A reading leaf proposes an equality, never a fact. The solver must independently prove
//! both operand domains and that equality before using it in the unchanged exhausted query.
//! Predicate binders are not entered. Negative contexts supply no domain assumption.

use super::{SmtPrelude, congruence::admit_graph};
use crate::{
    observation::reading::{Builder, Reading},
    rule::Predicate,
    stop::{self, Stoppable},
    term::{Term, TermKind, equal_terms_bounded},
};
use k_rust_kore::names::BuiltinSort;
use rustc_hash::FxHashSet;
use std::sync::Arc;

const WORK: usize = 4096;
pub(super) const TRIALS: usize = 16;
pub(super) const FACTS: usize = 8;

pub(super) struct Candidates {
    pub original: Term,
    pub leaves: Vec<Term>,
}

/// ```toml algorithm-site
/// id = "backend.smt.check"
/// role = "part"
/// sites = ["discover"]
/// ```
pub(super) fn discover(
    prelude: &SmtPrelude,
    checked: &[Predicate],
) -> Stoppable<Option<Vec<Candidates>>> {
    stop::check()?;
    let Some(source) = &prelude.source else {
        return Ok(None);
    };
    let definition = source.definition();
    let mut work = WORK;
    if checked.len() > work {
        return Ok(None);
    }
    let mut predicates = checked.iter().collect::<Vec<_>>();
    let mut roots = Vec::new();
    while let Some(predicate) = predicates.pop() {
        stop::check()?;
        if work == 0 {
            return Ok(None);
        }
        work -= 1;
        match predicate {
            Predicate::Term(t)
            | Predicate::Ceil(t)
            | Predicate::Floor(t)
            | Predicate::Defined(t) => roots.push(t),
            Predicate::Equals(a, b) | Predicate::In(a, b) => roots.extend([a, b]),
            Predicate::Not(p) => predicates.push(p),
            Predicate::And(parts) | Predicate::Or(parts) => {
                if parts.len() > work.saturating_sub(predicates.len() + roots.len()) {
                    return Ok(None);
                }
                predicates.extend(parts.iter());
            }
            Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                predicates.extend([a.as_ref(), b.as_ref()]);
            }
            Predicate::True
            | Predicate::False
            | Predicate::Exists(..)
            | Predicate::Forall(..)
            | Predicate::Absent(_) => {}
        }
        if predicates.len() + roots.len() > work {
            return Ok(None);
        }
    }
    // The existing observation builder uses value-keyed memos. Bound expanded visits first,
    // so small shared DAGs cannot send exponentially large structural comparisons into them.
    if !admit_graph(prelude, &roots, &mut work, None)? {
        return Ok(None);
    }
    let mut pending = roots;
    let mut seen = FxHashSet::default();
    let mut builder = Builder::new(definition);
    let mut result: Vec<Candidates> = Vec::new();
    let mut trials = 0;
    while let Some(term) = pending.pop() {
        stop::check()?;
        if work == 0 {
            return Ok(None);
        }
        work -= 1;
        if !seen.insert(term.node_address()) {
            continue;
        }
        let children = crate::term::immediate_children(term.kind());
        if children.len() > work.saturating_sub(pending.len()) {
            return Ok(None);
        }
        pending.extend(children);
        if !term.sort().is_builtin(BuiltinSort::Int) && !term.sort().is_builtin(BuiltinSort::Bool) {
            continue;
        }
        // Typed selectors and direct map observations retain their actual source contracts.
        // Arbitrary scalar helper heads compose using the proved leaf equalities afterward.
        let TermKind::Application {
            symbol, arguments, ..
        } = term.kind()
        else {
            continue;
        };
        let observation = match arguments.as_slice() {
            [input] => definition
                .selector(&input.sort(), &term.sort())
                .is_some_and(|s| s.project(input.clone()).as_ref() == Some(term)),
            [map, _] if symbol.attributes.hook.as_deref() == Some("MAP.lookup") => definition
                .map_operations(&map.sort())
                .is_some_and(|ops| ops.admits(term, "MAP.lookup")),
            [_, map] if symbol.attributes.hook.as_deref() == Some("MAP.in_keys") => definition
                .map_operations(&map.sort())
                .is_some_and(|ops| ops.admits(term, "MAP.in_keys")),
            _ => false,
        };
        if !observation {
            continue;
        }
        let mut duplicate = false;
        for previous in &result {
            match equal_terms_bounded(&previous.original, term, &mut work) {
                Some(true) => {
                    duplicate = true;
                    break;
                }
                Some(false) => {}
                None => return Ok(None),
            }
        }
        if duplicate {
            continue;
        }
        let Some(reading) = builder.of(term)? else {
            continue;
        };
        let mut readings = vec![reading];
        let mut read_seen = FxHashSet::default();
        let mut leaves = Vec::new();
        while let Some(reading) = readings.pop() {
            stop::check()?;
            if work == 0 {
                return Ok(None);
            }
            work -= 1;
            if !read_seen.insert(Arc::as_ptr(&reading) as usize) {
                continue;
            }
            match reading.as_ref() {
                Reading::Missing => {}
                Reading::If { yes, no, .. } => {
                    if readings.len() + 2 > work {
                        return Ok(None);
                    }
                    // Try the preserved base before written values; no path is assumed.
                    readings.extend([yes.clone(), no.clone()]);
                }
                Reading::Leaf(leaf) => {
                    if leaf.sort() != term.sort() {
                        continue;
                    }
                    match equal_terms_bounded(term, leaf, &mut work) {
                        Some(true) => continue,
                        Some(false) => {}
                        None => return Ok(None),
                    }
                    if !admit_graph(prelude, &[leaf], &mut work, None)? {
                        return Ok(None);
                    }
                    leaves.push(leaf.clone());
                    trials += 1;
                    if trials >= TRIALS {
                        break;
                    }
                }
            }
        }
        if !leaves.is_empty() {
            result.push(Candidates {
                original: term.clone(),
                leaves,
            });
        }
        if result.len() >= FACTS || trials >= TRIALS {
            break;
        }
    }
    Ok((!result.is_empty()).then_some(result))
}
