//! Finite map equality over source views. Outside the union of written/removed keys,
//! each view preserves its opaque base. Equality of those bases and the final observations
//! at that finite footprint therefore suffice for equality of the whole values.
//!
//! Footprint discovery visits each shared view node once and emits a fixed number of
//! observation requests per key. The existing reading builder shares their O(n*m) view
//! nodes for n writes and m requested keys; this is not a solver-time bound. Source hook
//! selection retains Operations' declaration scans. More than 128 keys or an exhausted
//! request budget declines the whole consequence, without dropping a footprint condition.

use std::{collections::BTreeSet, sync::Arc};

use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    stop::{self, Stoppable},
    term::Term,
};

use super::maps::{Operations, View};

pub(super) fn consequence(
    definition: &BackendDefinition,
    operations: &Operations,
    left: &Term,
    right: &Term,
    views: [Arc<View>; 2],
    remaining: &mut usize,
) -> Stoppable<Option<Predicate>> {
    let mut pending = Vec::from(views);
    let mut seen = BTreeSet::new();
    let mut bases = BTreeSet::new();
    let mut keys = BTreeSet::new();
    while let Some(view) = pending.pop() {
        stop::check()?;
        if !seen.insert(Arc::as_ptr(&view) as usize) {
            continue;
        }
        if *remaining == 0 {
            return Ok(None);
        }
        *remaining -= 1;
        match view.as_ref() {
            View::Base(base) => {
                bases.insert(base.clone());
            }
            View::Put { base, key, .. } | View::Remove { base, key } => {
                keys.insert(key.clone());
                if keys.len() > 128 {
                    return Ok(None);
                }
                pending.push(base.clone());
            }
            View::If { yes, no, .. } => pending.extend([yes.clone(), no.clone()]),
        }
    }
    // This is not a new extensionality axiom for arbitrary opaque maps. With no finite
    // changes there is no new source consequence to instantiate.
    if keys.is_empty() || keys.len().saturating_mul(8) > *remaining {
        return Ok(None);
    }
    *remaining -= keys.len() * 8;
    let Some(base) = bases.pop_first() else {
        return Ok(None);
    };
    let mut conditions = vec![
        Predicate::Ceil(left.clone()),
        Predicate::Ceil(right.clone()),
    ];
    // These are obligations, never aliases assumed from the equality being checked.
    // Requiring them is conservative for conditionals with different inactive bases.
    conditions.extend(
        bases
            .into_iter()
            .map(|other| Predicate::Equals(base.clone(), other)),
    );
    for key in keys {
        stop::check()?;
        let (Some(present_left), Some(present_right), Some(value_left), Some(value_right)) = (
            operations.member(definition, left.clone(), &key),
            operations.member(definition, right.clone(), &key),
            operations.lookup(definition, left.clone(), &key),
            operations.lookup(definition, right.clone(), &key),
        ) else {
            return Ok(None);
        };
        conditions.extend([
            Predicate::Ceil(present_left.clone()),
            Predicate::Ceil(present_right.clone()),
            Predicate::Equals(present_left.clone(), present_right),
            Predicate::Implies(
                Arc::new(Predicate::Term(present_left)),
                Arc::new(Predicate::And(
                    vec![
                        Predicate::Ceil(value_left.clone()),
                        Predicate::Ceil(value_right.clone()),
                        Predicate::Equals(value_left, value_right),
                    ]
                    .into(),
                )),
            ),
        ]);
    }
    Ok(Some(Predicate::Implies(
        Arc::new(Predicate::And(conditions.into())),
        Arc::new(Predicate::Equals(left.clone(), right.clone())),
    )))
}
