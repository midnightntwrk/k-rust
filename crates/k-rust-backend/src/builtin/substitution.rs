//! Capture-avoiding substitution of object-language `KVar` tokens.

use std::collections::{BTreeMap, BTreeSet};

use super::{BuiltinError, BuiltinResult, UnsupportedHookReason, check_interrupted, expect_arity};
use crate::{
    definition::BackendDefinition,
    matching::SortGraph,
    term::{Name, Sort, Term, TermKind},
};

pub(super) fn evaluate(
    hook: &str,
    arguments: &[Term],
    definition: Option<&BackendDefinition>,
) -> Result<BuiltinResult, BuiltinError> {
    match hook {
        "SUBSTITUTION.substOne" => {
            expect_arity(hook, arguments, 3)?;
            let Some(definition) = definition else {
                return Ok(BuiltinResult::NotApplicable);
            };
            let kvar_sorts = definition
                .sorts
                .iter()
                .filter(|(_, info)| info.hook.as_deref() == Some("KVAR.KVar"))
                .map(|(name, _)| name.clone())
                .collect::<BTreeSet<_>>();
            if kvar_sorts.is_empty() {
                return Ok(BuiltinResult::NotApplicable);
            }
            subst_one(arguments, &kvar_sorts, &definition.sort_graph)
        }
        "SUBSTITUTION.substMany" => Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        )),
        _ => Ok(BuiltinResult::Unsupported(
            UnsupportedHookReason::NotImplemented,
        )),
    }
}

fn subst_one(
    arguments: &[Term],
    kvar_sorts: &BTreeSet<Name>,
    sort_graph: &SortGraph,
) -> Result<BuiltinResult, BuiltinError> {
    let [body, replacement, variable] = arguments else {
        unreachable!("substOne arity was checked by the dispatcher")
    };
    let Some(target) = read_kvar(variable, kvar_sorts) else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let replacement = peel_injections(replacement);
    let Some(replacement_free) = free_kvars(&replacement, kvar_sorts)? else {
        return Ok(BuiltinResult::NotApplicable);
    };
    let mut used = BTreeSet::new();
    collect_kvars(body, kvar_sorts, &mut used)?;
    collect_kvars(&replacement, kvar_sorts, &mut used)?;
    used.insert(target.clone());
    let mut fresh = FreshNames {
        used,
        next_suffix: 0,
    };
    Ok(
        match substitute(
            body,
            &target,
            &replacement,
            &replacement_free,
            kvar_sorts,
            sort_graph,
            &mut fresh,
        )? {
            SubstituteOutcome::Value(term) => BuiltinResult::Value(term),
            SubstituteOutcome::NotApplicable => BuiltinResult::NotApplicable,
            SubstituteOutcome::Bottom => BuiltinResult::Bottom,
        },
    )
}

struct FreshNames {
    used: BTreeSet<Name>,
    next_suffix: u64,
}

impl FreshNames {
    fn mint(&mut self, base: &str) -> Name {
        loop {
            let candidate: Name = format!("{base}{}", self.next_suffix).into();
            self.next_suffix += 1;
            if self.used.insert(candidate.clone()) {
                return candidate;
            }
        }
    }
}

enum SubstituteOutcome {
    Value(Term),
    NotApplicable,
    Bottom,
}

macro_rules! substitution_value {
    ($result:expr) => {
        match $result? {
            SubstituteOutcome::Value(term) => term,
            SubstituteOutcome::NotApplicable => return Ok(SubstituteOutcome::NotApplicable),
            SubstituteOutcome::Bottom => return Ok(SubstituteOutcome::Bottom),
        }
    };
}

fn substitute(
    term: &Term,
    target: &Name,
    replacement: &Term,
    replacement_free: &BTreeSet<Name>,
    kvar_sorts: &BTreeSet<Name>,
    sort_graph: &SortGraph,
    fresh: &mut FreshNames,
) -> Result<SubstituteOutcome, BuiltinError> {
    check_interrupted()?;
    if read_kvar(term, kvar_sorts).as_ref() == Some(target) {
        return Ok(inject_to_sort(replacement.clone(), term.sort(), sort_graph)
            .map_or(SubstituteOutcome::NotApplicable, SubstituteOutcome::Value));
    }

    Ok(SubstituteOutcome::Value(match term.kind() {
        TermKind::And(left, right) => {
            let left = substitution_value!(substitute(
                left,
                target,
                replacement,
                replacement_free,
                kvar_sorts,
                sort_graph,
                fresh,
            ));
            let right = substitution_value!(substitute(
                right,
                target,
                replacement,
                replacement_free,
                kvar_sorts,
                sort_graph,
                fresh,
            ));
            Term::and(left, right)
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } if symbol.attributes.binder => {
            if arguments.len() < 2 {
                return Ok(SubstituteOutcome::NotApplicable);
            }
            let Some(bound) = read_kvar(&arguments[0], kvar_sorts) else {
                return Ok(SubstituteOutcome::NotApplicable);
            };
            let last = arguments.len() - 1;
            let mut updated = Vec::with_capacity(arguments.len());
            updated.push(arguments[0].clone());
            for argument in &arguments[1..last] {
                let argument = substitution_value!(substitute(
                    argument,
                    target,
                    replacement,
                    replacement_free,
                    kvar_sorts,
                    sort_graph,
                    fresh,
                ));
                updated.push(argument);
            }
            if &bound == target {
                updated.push(arguments[last].clone());
            } else {
                let mut body = arguments[last].clone();
                let Some(target_occurs) = contains_free_kvar(&body, target, kvar_sorts)? else {
                    return Ok(SubstituteOutcome::NotApplicable);
                };
                let mut effective_bound = bound.clone();
                if target_occurs && replacement_free.contains(&bound) {
                    let renamed = fresh.mint(&bound);
                    let declaration = rename_kvar_token(&updated[0], &renamed, kvar_sorts)
                        .expect("the binder declaration was validated as a KVar");
                    let renamed_token = peel_injections(&declaration);
                    let renamed_free = BTreeSet::from([renamed.clone()]);
                    let renamed_body = substitution_value!(substitute(
                        &body,
                        &bound,
                        &renamed_token,
                        &renamed_free,
                        kvar_sorts,
                        sort_graph,
                        fresh,
                    ));
                    updated[0] = declaration;
                    body = renamed_body;
                    effective_bound = renamed;
                }
                let hygienic_replacement;
                let replacement = if target_occurs {
                    let Some(value) = freshen_bound_kvar_identities(
                        replacement,
                        &effective_bound,
                        kvar_sorts,
                        fresh,
                    )?
                    else {
                        return Ok(SubstituteOutcome::NotApplicable);
                    };
                    hygienic_replacement = value;
                    &hygienic_replacement
                } else {
                    replacement
                };
                let body = substitution_value!(substitute(
                    &body,
                    target,
                    replacement,
                    replacement_free,
                    kvar_sorts,
                    sort_graph,
                    fresh,
                ));
                updated.push(body);
            }
            Term::application(symbol.clone(), sort_arguments.clone(), updated)
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => {
            let mut updated = Vec::with_capacity(arguments.len());
            for argument in arguments {
                updated.push(substitution_value!(substitute(
                    argument,
                    target,
                    replacement,
                    replacement_free,
                    kvar_sorts,
                    sort_graph,
                    fresh,
                )));
            }
            Term::application(symbol.clone(), sort_arguments.clone(), updated)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => term.clone(),
        TermKind::Injection {
            source,
            target: injection_target,
            term,
        } => {
            let inner = substitution_value!(substitute(
                term,
                target,
                replacement,
                replacement_free,
                kvar_sorts,
                sort_graph,
                fresh,
            ));
            Term::injection(source.clone(), injection_target.clone(), inner)
        }
        TermKind::Map {
            definition,
            entries,
            rest,
        } => {
            let mut updated_entries = Vec::with_capacity(entries.len());
            let mut key_changed = Vec::with_capacity(entries.len());
            for (key, value) in entries {
                let updated_key = substitution_value!(substitute(
                    key,
                    target,
                    replacement,
                    replacement_free,
                    kvar_sorts,
                    sort_graph,
                    fresh,
                ));
                let updated_value = substitution_value!(substitute(
                    value,
                    target,
                    replacement,
                    replacement_free,
                    kvar_sorts,
                    sort_graph,
                    fresh,
                ));
                key_changed.push(updated_key != *key);
                updated_entries.push((updated_key, updated_value));
            }
            for left in 0..updated_entries.len() {
                for right in left + 1..updated_entries.len() {
                    let left_key = &updated_entries[left].0;
                    let right_key = &updated_entries[right].0;
                    if left_key == right_key {
                        return Ok(SubstituteOutcome::Bottom);
                    }
                    if (key_changed[left] || key_changed[right])
                        && (!left_key.attributes().constructor_like
                            || !right_key.attributes().constructor_like)
                    {
                        return Ok(SubstituteOutcome::NotApplicable);
                    }
                }
            }
            if rest.is_some() && key_changed.iter().any(|changed| *changed) {
                return Ok(SubstituteOutcome::NotApplicable);
            }
            let rest = match rest {
                Some(rest) => {
                    let rest = substitution_value!(substitute(
                        rest,
                        target,
                        replacement,
                        replacement_free,
                        kvar_sorts,
                        sort_graph,
                        fresh,
                    ));
                    Some(rest)
                }
                None => None,
            };
            Term::map(definition.clone(), updated_entries, rest)
        }
        TermKind::List {
            definition,
            heads,
            rest,
        } => {
            let mut updated_heads = Vec::with_capacity(heads.len());
            for head in heads {
                updated_heads.push(substitution_value!(substitute(
                    head,
                    target,
                    replacement,
                    replacement_free,
                    kvar_sorts,
                    sort_graph,
                    fresh,
                )));
            }
            let rest = match rest {
                Some((middle, tails)) => {
                    let middle = substitution_value!(substitute(
                        middle,
                        target,
                        replacement,
                        replacement_free,
                        kvar_sorts,
                        sort_graph,
                        fresh,
                    ));
                    let mut updated_tails = Vec::with_capacity(tails.len());
                    for tail in tails {
                        updated_tails.push(substitution_value!(substitute(
                            tail,
                            target,
                            replacement,
                            replacement_free,
                            kvar_sorts,
                            sort_graph,
                            fresh,
                        )));
                    }
                    Some((middle, updated_tails))
                }
                None => None,
            };
            Term::list(definition.clone(), updated_heads, rest)
        }
        TermKind::Set {
            definition,
            elements,
            rest,
        } => {
            let mut updated_elements = Vec::with_capacity(elements.len());
            for element in elements {
                updated_elements.push(substitution_value!(substitute(
                    element,
                    target,
                    replacement,
                    replacement_free,
                    kvar_sorts,
                    sort_graph,
                    fresh,
                )));
            }
            let rest = match rest {
                Some(rest) => {
                    let rest = substitution_value!(substitute(
                        rest,
                        target,
                        replacement,
                        replacement_free,
                        kvar_sorts,
                        sort_graph,
                        fresh,
                    ));
                    Some(rest)
                }
                None => None,
            };
            Term::set(definition.clone(), updated_elements, rest)
        }
    }))
}

fn freshen_bound_kvar_identities(
    term: &Term,
    conflict: &Name,
    kvar_sorts: &BTreeSet<Name>,
    fresh: &mut FreshNames,
) -> Result<Option<Term>, BuiltinError> {
    freshen_bound_kvar_identities_inner(term, conflict, kvar_sorts, fresh, &mut Vec::new())
}

fn freshen_bound_kvar_identities_inner(
    term: &Term,
    conflict: &Name,
    kvar_sorts: &BTreeSet<Name>,
    fresh: &mut FreshNames,
    bound_renamings: &mut Vec<Name>,
) -> Result<Option<Term>, BuiltinError> {
    check_interrupted()?;
    if read_kvar(term, kvar_sorts).as_ref() == Some(conflict) {
        let Some(renamed) = bound_renamings.last() else {
            return Ok(Some(term.clone()));
        };
        return Ok(rename_kvar_token(term, renamed, kvar_sorts));
    }

    Ok(Some(match term.kind() {
        TermKind::And(left, right) => {
            let Some(left) = freshen_bound_kvar_identities_inner(
                left,
                conflict,
                kvar_sorts,
                fresh,
                bound_renamings,
            )?
            else {
                return Ok(None);
            };
            let Some(right) = freshen_bound_kvar_identities_inner(
                right,
                conflict,
                kvar_sorts,
                fresh,
                bound_renamings,
            )?
            else {
                return Ok(None);
            };
            Term::and(left, right)
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } if symbol.attributes.binder => {
            if arguments.len() < 2 {
                return Ok(None);
            }
            let Some(bound) = read_kvar(&arguments[0], kvar_sorts) else {
                return Ok(None);
            };
            let last = arguments.len() - 1;
            let mut updated = Vec::with_capacity(arguments.len());
            if &bound == conflict {
                let renamed = fresh.mint(&bound);
                updated.push(
                    rename_kvar_token(&arguments[0], &renamed, kvar_sorts)
                        .expect("the binder declaration was validated as a KVar"),
                );
                for argument in &arguments[1..last] {
                    let Some(argument) = freshen_bound_kvar_identities_inner(
                        argument,
                        conflict,
                        kvar_sorts,
                        fresh,
                        bound_renamings,
                    )?
                    else {
                        return Ok(None);
                    };
                    updated.push(argument);
                }
                bound_renamings.push(renamed);
                let body = freshen_bound_kvar_identities_inner(
                    &arguments[last],
                    conflict,
                    kvar_sorts,
                    fresh,
                    bound_renamings,
                )?;
                bound_renamings.pop();
                let Some(body) = body else {
                    return Ok(None);
                };
                updated.push(body);
            } else {
                updated.push(arguments[0].clone());
                for argument in &arguments[1..] {
                    let Some(argument) = freshen_bound_kvar_identities_inner(
                        argument,
                        conflict,
                        kvar_sorts,
                        fresh,
                        bound_renamings,
                    )?
                    else {
                        return Ok(None);
                    };
                    updated.push(argument);
                }
            }
            Term::application(symbol.clone(), sort_arguments.clone(), updated)
        }
        TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } => {
            let Some(arguments) = arguments
                .iter()
                .map(|argument| {
                    freshen_bound_kvar_identities_inner(
                        argument,
                        conflict,
                        kvar_sorts,
                        fresh,
                        bound_renamings,
                    )
                })
                .collect::<Result<Option<Vec<_>>, _>>()?
            else {
                return Ok(None);
            };
            Term::application(symbol.clone(), sort_arguments.clone(), arguments)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => term.clone(),
        TermKind::Injection {
            source,
            target,
            term,
        } => {
            let Some(inner) = freshen_bound_kvar_identities_inner(
                term,
                conflict,
                kvar_sorts,
                fresh,
                bound_renamings,
            )?
            else {
                return Ok(None);
            };
            Term::injection(source.clone(), target.clone(), inner)
        }
        TermKind::Map {
            definition,
            entries,
            rest,
        } => {
            let Some(entries) = entries
                .iter()
                .map(|(key, value)| {
                    Ok(freshen_bound_kvar_identities_inner(
                        key,
                        conflict,
                        kvar_sorts,
                        fresh,
                        bound_renamings,
                    )?
                    .zip(freshen_bound_kvar_identities_inner(
                        value,
                        conflict,
                        kvar_sorts,
                        fresh,
                        bound_renamings,
                    )?))
                })
                .collect::<Result<Option<Vec<_>>, BuiltinError>>()?
            else {
                return Ok(None);
            };
            let rest = match rest {
                Some(rest) => {
                    let Some(rest) = freshen_bound_kvar_identities_inner(
                        rest,
                        conflict,
                        kvar_sorts,
                        fresh,
                        bound_renamings,
                    )?
                    else {
                        return Ok(None);
                    };
                    Some(rest)
                }
                None => None,
            };
            Term::map(definition.clone(), entries, rest)
        }
        TermKind::List {
            definition,
            heads,
            rest,
        } => {
            let Some(heads) = heads
                .iter()
                .map(|head| {
                    freshen_bound_kvar_identities_inner(
                        head,
                        conflict,
                        kvar_sorts,
                        fresh,
                        bound_renamings,
                    )
                })
                .collect::<Result<Option<Vec<_>>, _>>()?
            else {
                return Ok(None);
            };
            let rest = match rest {
                Some((middle, tails)) => {
                    let Some(middle) = freshen_bound_kvar_identities_inner(
                        middle,
                        conflict,
                        kvar_sorts,
                        fresh,
                        bound_renamings,
                    )?
                    else {
                        return Ok(None);
                    };
                    let Some(tails) = tails
                        .iter()
                        .map(|tail| {
                            freshen_bound_kvar_identities_inner(
                                tail,
                                conflict,
                                kvar_sorts,
                                fresh,
                                bound_renamings,
                            )
                        })
                        .collect::<Result<Option<Vec<_>>, _>>()?
                    else {
                        return Ok(None);
                    };
                    Some((middle, tails))
                }
                None => None,
            };
            Term::list(definition.clone(), heads, rest)
        }
        TermKind::Set {
            definition,
            elements,
            rest,
        } => {
            let Some(elements) = elements
                .iter()
                .map(|element| {
                    freshen_bound_kvar_identities_inner(
                        element,
                        conflict,
                        kvar_sorts,
                        fresh,
                        bound_renamings,
                    )
                })
                .collect::<Result<Option<Vec<_>>, _>>()?
            else {
                return Ok(None);
            };
            let rest = match rest {
                Some(rest) => {
                    let Some(rest) = freshen_bound_kvar_identities_inner(
                        rest,
                        conflict,
                        kvar_sorts,
                        fresh,
                        bound_renamings,
                    )?
                    else {
                        return Ok(None);
                    };
                    Some(rest)
                }
                None => None,
            };
            Term::set(definition.clone(), elements, rest)
        }
    }))
}

fn free_kvars(
    term: &Term,
    kvar_sorts: &BTreeSet<Name>,
) -> Result<Option<BTreeSet<Name>>, BuiltinError> {
    let mut free = BTreeSet::new();
    let mut bound = BTreeMap::new();
    if collect_free_kvars(term, kvar_sorts, &mut bound, &mut free)? {
        Ok(Some(free))
    } else {
        Ok(None)
    }
}

fn contains_free_kvar(
    term: &Term,
    target: &Name,
    kvar_sorts: &BTreeSet<Name>,
) -> Result<Option<bool>, BuiltinError> {
    Ok(free_kvars(term, kvar_sorts)?.map(|free| free.contains(target)))
}

fn collect_free_kvars(
    term: &Term,
    kvar_sorts: &BTreeSet<Name>,
    bound: &mut BTreeMap<Name, usize>,
    free: &mut BTreeSet<Name>,
) -> Result<bool, BuiltinError> {
    check_interrupted()?;
    if let Some(name) = read_kvar(term, kvar_sorts) {
        if !bound.contains_key(&name) {
            free.insert(name);
        }
        return Ok(true);
    }
    match term.kind() {
        TermKind::And(left, right) => Ok(collect_free_kvars(left, kvar_sorts, bound, free)?
            && collect_free_kvars(right, kvar_sorts, bound, free)?),
        TermKind::Application {
            symbol, arguments, ..
        } if symbol.attributes.binder => {
            if arguments.len() < 2 {
                return Ok(false);
            }
            let Some(name) = read_kvar(&arguments[0], kvar_sorts) else {
                return Ok(false);
            };
            for argument in &arguments[1..arguments.len() - 1] {
                if !collect_free_kvars(argument, kvar_sorts, bound, free)? {
                    return Ok(false);
                }
            }
            *bound.entry(name.clone()).or_default() += 1;
            let valid = collect_free_kvars(
                arguments
                    .last()
                    .expect("a binder has at least two arguments"),
                kvar_sorts,
                bound,
                free,
            )?;
            let count = bound.get_mut(&name).expect("the binder count was inserted");
            *count -= 1;
            if *count == 0 {
                bound.remove(&name);
            }
            Ok(valid)
        }
        TermKind::Application { arguments, .. } => {
            for argument in arguments {
                if !collect_free_kvars(argument, kvar_sorts, bound, free)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => Ok(true),
        TermKind::Injection { term, .. } => collect_free_kvars(term, kvar_sorts, bound, free),
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                if !collect_free_kvars(key, kvar_sorts, bound, free)?
                    || !collect_free_kvars(value, kvar_sorts, bound, free)?
                {
                    return Ok(false);
                }
            }
            if let Some(rest) = rest {
                collect_free_kvars(rest, kvar_sorts, bound, free)
            } else {
                Ok(true)
            }
        }
        TermKind::List { heads, rest, .. } => {
            for head in heads {
                if !collect_free_kvars(head, kvar_sorts, bound, free)? {
                    return Ok(false);
                }
            }
            if let Some((middle, tails)) = rest {
                if !collect_free_kvars(middle, kvar_sorts, bound, free)? {
                    return Ok(false);
                }
                for tail in tails {
                    if !collect_free_kvars(tail, kvar_sorts, bound, free)? {
                        return Ok(false);
                    }
                }
            }
            Ok(true)
        }
        TermKind::Set { elements, rest, .. } => {
            for element in elements {
                if !collect_free_kvars(element, kvar_sorts, bound, free)? {
                    return Ok(false);
                }
            }
            if let Some(rest) = rest {
                collect_free_kvars(rest, kvar_sorts, bound, free)
            } else {
                Ok(true)
            }
        }
    }
}

fn collect_kvars(
    term: &Term,
    kvar_sorts: &BTreeSet<Name>,
    names: &mut BTreeSet<Name>,
) -> Result<(), BuiltinError> {
    check_interrupted()?;
    if let Some(name) = read_kvar(term, kvar_sorts) {
        names.insert(name);
        return Ok(());
    }
    match term.kind() {
        TermKind::And(left, right) => {
            collect_kvars(left, kvar_sorts, names)?;
            collect_kvars(right, kvar_sorts, names)?;
        }
        TermKind::Application { arguments, .. } => {
            for argument in arguments {
                collect_kvars(argument, kvar_sorts, names)?;
            }
        }
        TermKind::DomainValue { .. } | TermKind::Variable(_) => {}
        TermKind::Injection { term, .. } => collect_kvars(term, kvar_sorts, names)?,
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                collect_kvars(key, kvar_sorts, names)?;
                collect_kvars(value, kvar_sorts, names)?;
            }
            if let Some(rest) = rest {
                collect_kvars(rest, kvar_sorts, names)?;
            }
        }
        TermKind::List { heads, rest, .. } => {
            for head in heads {
                collect_kvars(head, kvar_sorts, names)?;
            }
            if let Some((middle, tails)) = rest {
                collect_kvars(middle, kvar_sorts, names)?;
                for tail in tails {
                    collect_kvars(tail, kvar_sorts, names)?;
                }
            }
        }
        TermKind::Set { elements, rest, .. } => {
            for element in elements {
                collect_kvars(element, kvar_sorts, names)?;
            }
            if let Some(rest) = rest {
                collect_kvars(rest, kvar_sorts, names)?;
            }
        }
    }
    Ok(())
}

fn read_kvar(term: &Term, kvar_sorts: &BTreeSet<Name>) -> Option<Name> {
    match term.kind() {
        TermKind::DomainValue {
            sort: Sort::Application { name, arguments },
            value,
        } if arguments.is_empty() && kvar_sorts.contains(name) => Some(value.clone()),
        TermKind::Injection { term, .. } => read_kvar(term, kvar_sorts),
        _ => None,
    }
}

fn rename_kvar_token(term: &Term, new: &Name, kvar_sorts: &BTreeSet<Name>) -> Option<Term> {
    match term.kind() {
        TermKind::DomainValue {
            sort: Sort::Application { name, arguments },
            ..
        } if arguments.is_empty() && kvar_sorts.contains(name) => {
            Some(Term::domain_value(term.sort(), new.clone()))
        }
        TermKind::Injection {
            source,
            target,
            term,
        } => Some(Term::injection(
            source.clone(),
            target.clone(),
            rename_kvar_token(term, new, kvar_sorts)?,
        )),
        _ => None,
    }
}

fn peel_injections(term: &Term) -> Term {
    let mut term = term;
    while let TermKind::Injection { term: inner, .. } = term.kind() {
        term = inner;
    }
    term.clone()
}

fn inject_to_sort(term: Term, target: Sort, sorts: &SortGraph) -> Option<Term> {
    let source = term.sort();
    if source == target {
        return Some(term);
    }
    sorts
        .check_subsort(&source, &target)
        .ok()?
        .then(|| Term::injection(source, target, term))
}

#[cfg(test)]
mod tests {
    use std::{sync::Arc, time::Duration};

    use indoc::indoc;
    use k_rust_kore::kore::parser::parse_definition;

    use super::*;
    use crate::{
        term::{CollectionSymbols, ListDefinition, MapDefinition, Symbol},
        timeout::{StepTimeoutController, StepTimeoutOptions},
    };

    fn kvar_sort() -> Sort {
        Sort::simple("SortKVar")
    }

    fn exp_sort() -> Sort {
        Sort::simple("SortExp")
    }

    fn val_sort() -> Sort {
        Sort::simple("SortVal")
    }

    fn kvar_sorts() -> BTreeSet<Name> {
        BTreeSet::from(["SortKVar".into()])
    }

    fn sort_graph() -> SortGraph {
        let mut graph = SortGraph::default();
        graph.insert("SortKVar", ["SortKVar".into()]);
        graph.insert("SortVal", ["SortVal".into()]);
        graph.insert(
            "SortExp",
            ["SortExp".into(), "SortKVar".into(), "SortVal".into()],
        );
        graph.insert(
            "SortKItem",
            [
                "SortKItem".into(),
                "SortExp".into(),
                "SortKVar".into(),
                "SortVal".into(),
            ],
        );
        graph
    }

    fn kvar(name: &str) -> Term {
        Term::domain_value(kvar_sort(), name)
    }

    fn exp_var(name: &str) -> Term {
        Term::injection(kvar_sort(), exp_sort(), kvar(name))
    }

    fn lambda(name: &str, body: Term) -> Term {
        let mut symbol = Symbol::constructor("lambda", vec![kvar_sort(), exp_sort()], val_sort());
        symbol.attributes.binder = true;
        Term::application(Arc::new(symbol), Vec::new(), vec![kvar(name), body])
    }

    fn apply(left: Term, right: Term) -> Term {
        Term::application(
            Arc::new(Symbol::constructor(
                "apply",
                vec![exp_sort(), exp_sort()],
                exp_sort(),
            )),
            Vec::new(),
            vec![left, right],
        )
    }

    fn test_map_definition() -> Arc<MapDefinition> {
        Arc::new(MapDefinition {
            symbols: CollectionSymbols {
                unit: "map-unit".into(),
                element: "map-element".into(),
                concat: "map-concat".into(),
            },
            key_sort: "SortExp".into(),
            value_sort: "SortExp".into(),
            map_sort: "SortMap".into(),
        })
    }

    fn run(body: Term, replacement: Term, target: Term) -> BuiltinResult {
        subst_one(&[body, replacement, target], &kvar_sorts(), &sort_graph()).unwrap()
    }

    #[test]
    fn replaces_free_kvars_and_preserves_absent_terms() {
        assert_eq!(
            run(kvar("x"), kvar("y"), kvar("x")),
            BuiltinResult::Value(kvar("y"))
        );
        assert_eq!(
            run(kvar("z"), kvar("y"), kvar("x")),
            BuiltinResult::Value(kvar("z"))
        );
    }

    #[test]
    fn respects_shadowing_and_avoids_capture() {
        let shadowed = lambda("x", exp_var("x"));
        assert_eq!(
            run(shadowed.clone(), kvar("y"), kvar("x")),
            BuiltinResult::Value(shadowed)
        );

        assert_eq!(
            run(lambda("y", exp_var("x")), kvar("y"), kvar("x")),
            BuiltinResult::Value(lambda("y0", exp_var("y")))
        );
        assert_eq!(
            run(lambda("y", exp_var("x")), kvar("y0"), kvar("x")),
            BuiltinResult::Value(lambda("y", exp_var("y0")))
        );
    }

    #[test]
    fn renames_only_occurrences_owned_by_the_conflicting_binder() {
        let body = lambda(
            "y",
            apply(exp_var("x"), lambda("y", apply(exp_var("y"), exp_var("x")))),
        );
        let expected = lambda(
            "y0",
            apply(
                exp_var("y"),
                lambda("y1", apply(exp_var("y1"), exp_var("y"))),
            ),
        );
        assert_eq!(
            run(body, kvar("y"), kvar("x")),
            BuiltinResult::Value(expected)
        );
    }

    #[test]
    fn handles_closed_replacements_and_distinct_nested_binders() {
        let closed = lambda("z", exp_var("z"));
        let body = lambda("y", exp_var("x"));
        assert_eq!(
            run(body, closed.clone(), kvar("x")),
            BuiltinResult::Value(lambda("y", Term::injection(val_sort(), exp_sort(), closed)))
        );

        let colliding = lambda("x", lambda("y", apply(exp_var("x"), exp_var("y"))));
        assert_eq!(
            run(lambda("y", exp_var("q")), colliding, kvar("q")),
            BuiltinResult::Value(lambda(
                "y",
                Term::injection(
                    val_sort(),
                    exp_sort(),
                    lambda("x", lambda("y0", apply(exp_var("x"), exp_var("y0"))))
                )
            ))
        );

        let replacement = apply(exp_var("y"), exp_var("z"));
        let body = lambda("y", lambda("z", exp_var("x")));
        let expected = lambda("y0", lambda("z1", replacement.clone()));
        assert_eq!(
            run(body, replacement, kvar("x")),
            BuiltinResult::Value(expected)
        );
    }

    #[test]
    fn aligns_replacements_to_the_occurrence_sort() {
        let replacement = Term::injection(
            val_sort(),
            Sort::simple("SortKItem"),
            lambda("z", exp_var("z")),
        );
        let expected = Term::injection(val_sort(), exp_sort(), lambda("z", exp_var("z")));
        assert_eq!(
            run(exp_var("x"), replacement, kvar("x")),
            BuiltinResult::Value(expected)
        );
        assert_eq!(
            run(
                kvar("x"),
                Term::injection(kvar_sort(), Sort::simple("SortKItem"), kvar("y")),
                kvar("x")
            ),
            BuiltinResult::Value(kvar("y"))
        );
    }

    #[test]
    fn traverses_maps_lists_and_sets() {
        let map_definition = test_map_definition();
        let list_definition = Arc::new(ListDefinition {
            symbols: CollectionSymbols {
                unit: "list-unit".into(),
                element: "list-element".into(),
                concat: "list-concat".into(),
            },
            element_sort: "SortExp".into(),
            list_sort: "SortList".into(),
        });
        let map = Term::map(
            map_definition.clone(),
            vec![(exp_var("z"), exp_var("x"))],
            Some(exp_var("x")),
        );
        let list = Term::list(
            list_definition.clone(),
            vec![exp_var("x")],
            Some((exp_var("x"), vec![exp_var("x")])),
        );
        let set = Term::set(
            list_definition.clone(),
            vec![exp_var("x")],
            Some(exp_var("x")),
        );
        assert_eq!(
            run(map, kvar("y"), kvar("x")),
            BuiltinResult::Value(Term::map(
                map_definition,
                vec![(exp_var("z"), exp_var("y"))],
                Some(exp_var("y"))
            ))
        );
        assert_eq!(
            run(list, kvar("y"), kvar("x")),
            BuiltinResult::Value(Term::list(
                list_definition.clone(),
                vec![exp_var("y")],
                Some((exp_var("y"), vec![exp_var("y")]))
            ))
        );
        assert_eq!(
            run(set, kvar("y"), kvar("x")),
            BuiltinResult::Value(Term::set(
                list_definition,
                vec![exp_var("y")],
                Some(exp_var("y"))
            ))
        );
    }

    #[test]
    fn returns_bottom_when_substitution_duplicates_a_map_key() {
        let definition = test_map_definition();
        let map = Term::map(
            definition,
            vec![(exp_var("x"), exp_var("a")), (exp_var("y"), exp_var("b"))],
            None,
        );

        assert_eq!(run(map, kvar("y"), kvar("x")), BuiltinResult::Bottom);
    }

    #[test]
    fn rejects_a_changed_map_key_with_unresolved_equality() {
        let definition = test_map_definition();
        let symbolic_key = Term::variable(crate::term::Variable::new("KEY", exp_sort()));
        let map = Term::map(
            definition,
            vec![(exp_var("x"), exp_var("a")), (symbolic_key, exp_var("b"))],
            None,
        );

        assert_eq!(run(map, kvar("y"), kvar("x")), BuiltinResult::NotApplicable);
    }

    #[test]
    fn preserves_distinct_constructor_like_map_keys() {
        let definition = test_map_definition();
        let map = Term::map(
            definition.clone(),
            vec![(exp_var("x"), exp_var("a")), (exp_var("y"), exp_var("b"))],
            None,
        );
        let expected = Term::map(
            definition,
            vec![(exp_var("z"), exp_var("a")), (exp_var("y"), exp_var("b"))],
            None,
        );

        assert_eq!(
            run(map, kvar("z"), kvar("x")),
            BuiltinResult::Value(expected)
        );
    }

    #[test]
    fn rejects_a_changed_map_key_with_a_symbolic_remainder() {
        let definition = test_map_definition();
        let symbolic_rest =
            Term::variable(crate::term::Variable::new("REST", Sort::simple("SortMap")));
        let map = Term::map(
            definition,
            vec![(exp_var("x"), exp_var("a"))],
            Some(symbolic_rest),
        );

        assert_eq!(run(map, kvar("y"), kvar("x")), BuiltinResult::NotApplicable);
    }

    #[test]
    fn rejects_malformed_or_symbolic_inputs_without_partial_substitution() {
        let malformed_shape = {
            let mut symbol = Symbol::constructor("bad-binder", vec![kvar_sort()], val_sort());
            symbol.attributes.binder = true;
            Term::application(Arc::new(symbol), Vec::new(), vec![kvar("x")])
        };
        assert_eq!(
            run(malformed_shape, kvar("y"), kvar("x")),
            BuiltinResult::NotApplicable
        );
        let malformed_declaration = {
            let mut symbol =
                Symbol::constructor("bad-binder", vec![exp_sort(), exp_sort()], val_sort());
            symbol.attributes.binder = true;
            Term::application(
                Arc::new(symbol),
                Vec::new(),
                vec![apply(exp_var("x"), exp_var("x")), exp_var("x")],
            )
        };
        assert_eq!(
            run(malformed_declaration, kvar("y"), kvar("x")),
            BuiltinResult::NotApplicable
        );
        assert_eq!(
            run(
                kvar("x"),
                kvar("y"),
                Term::variable(crate::term::Variable::new("X", kvar_sort()))
            ),
            BuiltinResult::NotApplicable
        );
    }

    #[test]
    fn enforces_subst_one_arity_and_keeps_subst_many_unsupported() {
        let arguments = [kvar("x"), kvar("y")];
        assert_eq!(
            evaluate("SUBSTITUTION.substOne", &arguments, None),
            Err(BuiltinError::WrongArity {
                hook: "SUBSTITUTION.substOne".into(),
                expected: 3,
                actual: 2,
            })
        );
        assert_eq!(
            evaluate("SUBSTITUTION.substMany", &arguments, None),
            Ok(BuiltinResult::Unsupported(
                UnsupportedHookReason::NotImplemented
            ))
        );
    }

    #[test]
    fn evaluates_subst_one_with_definition_metadata() {
        let syntax = parse_definition(indoc! {r#"
            []
            module MAIN
                hooked-sort SortKVar{} [hook{}("KVAR.KVar"), hasDomainValues{}()]
                hooked-symbol substOne{}(SortKVar{}, SortKVar{}, SortKVar{}) : SortKVar{}
                    [function{}(), total{}(), hook{}("SUBSTITUTION.substOne")]
            endmodule []
        "#})
        .expect("definition should parse");
        let definition =
            BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize");
        let application = Term::application(
            definition.symbols["substOne"].clone(),
            Vec::new(),
            vec![kvar("x"), kvar("y"), kvar("x")],
        );

        assert_eq!(
            crate::builtin::evaluate_in_definition(&application, &definition),
            Ok(BuiltinResult::Value(kvar("y")))
        );
    }

    #[test]
    fn observes_the_active_step_deadline() {
        let controller = StepTimeoutController::new(StepTimeoutOptions {
            manual: Some(Duration::ZERO),
            moving_average: false,
        });
        let _timer = controller.begin_step();
        assert_eq!(
            subst_one(
                &[kvar("x"), kvar("y"), kvar("x")],
                &kvar_sorts(),
                &sort_graph()
            ),
            Err(BuiltinError::Interrupted)
        );
    }
}
