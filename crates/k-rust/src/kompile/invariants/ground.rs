//! Agreement between a ground value's typing and the symbol instances injection emits.
//!
//! A parametric macro rule describes one symbol instance, so macro selection at the value's
//! position must compare the instance that the emitted value contains. Injection may insert
//! wrappers and change paths; the multiset preserves every application's multiplicity without
//! depending on those paths.

use std::collections::BTreeMap;

use crate::definition::{LabelHead, ProductionCatalog, Sentence};
use crate::kast::{Label, Sort, Term};
use crate::kompile::sort_injections::{SentenceTyper, SortInjector};

type Instances = BTreeMap<(String, Vec<Option<Sort>>), usize>;

/// Check G2-ground after expansion. Typing or injection errors are reported by compilation,
/// so neither is a checker violation.
pub(crate) fn assert_ground_instances(
    productions: &ProductionCatalog<'_>,
    typer: &SentenceTyper<'_>,
    injector: &SortInjector<'_, '_>,
    term: &Term,
    position: &Sort,
) {
    let Ok(typing) = typer.ground_typing(term, position) else {
        return;
    };
    let Ok(sort) = injector.term_sort(term, Some(position)) else {
        return;
    };
    let Ok(injected) = injector.inject(term, &sort) else {
        return;
    };

    let mut typed = Instances::new();
    for (path, parameters) in &typing.instances {
        let Some((0, body_path)) = path.split_first() else {
            continue;
        };
        let Some(Term::Apply { label, .. }) = at_path(term, body_path).map(Term::unannotated)
        else {
            continue;
        };
        if parametric(productions, label) {
            let parameters = parameters
                .iter()
                .map(|parameter| parameter.as_ref().and_then(closed))
                .collect();
            *typed.entry((label.name.clone(), parameters)).or_default() += 1;
        }
    }

    let mut emitted = Instances::new();
    injected.visit_preorder(&mut |term| {
        if let Term::Apply { label, .. } = term.unannotated()
            && parametric(productions, label)
        {
            let parameters = label.parameters.iter().map(closed).collect();
            *emitted.entry((label.name.clone(), parameters)).or_default() += 1;
        }
    });

    if let Some(entry) = typed
        .keys()
        .chain(emitted.keys())
        .find(|entry| typed.get(*entry) != emitted.get(*entry))
    {
        panic!(
            "G2 ground instance agreement at position {position:?}: first differing entry \
             {entry:?}, typing count {}, injection count {}",
            typed.get(entry).copied().unwrap_or(0),
            emitted.get(entry).copied().unwrap_or(0),
        );
    }
}

fn parametric(productions: &ProductionCatalog<'_>, label: &Label) -> bool {
    let Some(id) = productions.productions_for(&LabelHead::from(label)).first() else {
        return false;
    };
    matches!(productions.production(*id), Sentence::Production { parameters, .. } if !parameters.is_empty())
}

fn closed(sort: &Sort) -> Option<Sort> {
    fn mentions_variable(sort: &Sort) -> bool {
        sort.is_rigid_variable() || sort.parameters.iter().any(mentions_variable)
    }
    (!mentions_variable(sort)).then(|| sort.clone())
}

fn at_path<'a>(mut term: &'a Term, path: &[u32]) -> Option<&'a Term> {
    for &step in path {
        let index = usize::try_from(step).ok()?;
        term = match term.unannotated() {
            Term::Apply { arguments, .. } => arguments.get(index)?,
            Term::Sequence(items) => items.get(index)?,
            Term::Rewrite { left, right } => [left.as_ref(), right.as_ref()].get(index).copied()?,
            Term::As { pattern, alias } => {
                [pattern.as_ref(), alias.as_ref()].get(index).copied()?
            }
            Term::InjectedLabel(_)
            | Term::Variable { .. }
            | Term::Token { .. }
            | Term::Annotated { .. } => return None,
        };
    }
    Some(term)
}
