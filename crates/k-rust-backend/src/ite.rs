//! Shared symbolic `KEQUAL.ite` splitting at unification boundaries.

use crate::term::{Term, TermKind};

#[derive(Clone, Copy)]
pub(crate) enum SplitSide {
    Pattern,
    Subject,
}

pub(crate) struct IteSplit {
    pub(crate) side: SplitSide,
    pub(crate) condition: Term,
    pub(crate) then_pair: (Term, Term),
    pub(crate) else_pair: (Term, Term),
}

pub(crate) fn split_ite_pair(pattern: &Term, subject: &Term) -> Option<IteSplit> {
    if let Some((condition, then_branch, else_branch)) = ite_arguments(pattern) {
        return Some(IteSplit {
            side: SplitSide::Pattern,
            condition,
            then_pair: (then_branch, subject.clone()),
            else_pair: (else_branch, subject.clone()),
        });
    }
    let (condition, then_branch, else_branch) = ite_arguments(subject)?;
    Some(IteSplit {
        side: SplitSide::Subject,
        condition,
        then_pair: (pattern.clone(), then_branch),
        else_pair: (pattern.clone(), else_branch),
    })
}

pub(crate) fn ite_arguments(term: &Term) -> Option<(Term, Term, Term)> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    if symbol.attributes.hook.as_deref() != Some("KEQUAL.ite") {
        return None;
    }
    let [condition, then_branch, else_branch] = arguments.as_slice() else {
        return None;
    };
    Some((condition.clone(), then_branch.clone(), else_branch.clone()))
}
