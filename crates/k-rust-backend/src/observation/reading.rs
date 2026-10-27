//! Bounded source observation DAGs. Leaves and tests contain only source terms/predicates;
//! these plans never hold caller facts, solver names, or an invented strict K conditional.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    stop::{self, Stoppable},
    term::{HeadRole, Term, TermKind},
};

use super::maps::{self, View, Views};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Reading {
    Leaf(Term),
    Missing,
    If {
        test: Predicate,
        yes: Arc<Self>,
        no: Arc<Self>,
    },
}

fn choice(test: Predicate, yes: Arc<Reading>, no: Arc<Reading>) -> Arc<Reading> {
    match test {
        Predicate::True => yes,
        Predicate::False => no,
        _ if Arc::ptr_eq(&yes, &no)
            || matches!((yes.as_ref(), no.as_ref()), (Reading::Leaf(a), Reading::Leaf(b)) if a == b) =>
        {
            yes
        }
        _ => Arc::new(Reading::If { test, yes, no }),
    }
}

/// Equality of stored keys, using only licensed injection cancellation and existing
/// solver-free apartness. Unknown aliases remain ordinary equality obligations.
pub(crate) fn key_equal(definition: &BackendDefinition, a: &Term, b: &Term) -> Predicate {
    if a == b {
        return Predicate::True;
    }
    if crate::builtin::values_differ(Some(definition.sort_graph()), a, b) {
        return Predicate::False;
    }
    if let (
        TermKind::Injection {
            source: sa,
            target: ta,
            term: a,
        },
        TermKind::Injection {
            source: sb,
            target: tb,
            term: b,
        },
    ) = (a.kind(), b.kind())
        && sa == sb
        && ta == tb
        && definition.sort_graph().check_subsort(sa, ta) == Ok(true)
    {
        return key_equal(definition, a, b);
    }
    Predicate::Equals(a.clone(), b.clone())
}

pub(crate) struct Builder<'a> {
    definition: &'a BackendDefinition,
    maps: BTreeMap<crate::term::Sort, Views<'a>>,
    memo: BTreeMap<Term, Option<Arc<Reading>>>,
    observations: BTreeMap<(usize, Term), Arc<Reading>>,
    pure: BTreeMap<Term, bool>,
    effects: Option<BTreeSet<String>>,
    remaining: usize,
}

impl<'a> Builder<'a> {
    pub fn new(definition: &'a BackendDefinition) -> Self {
        Self {
            definition,
            maps: BTreeMap::new(),
            memo: BTreeMap::new(),
            observations: BTreeMap::new(),
            pure: BTreeMap::new(),
            effects: definition.console_effect_symbols(),
            remaining: 16_384,
        }
    }

    pub fn of(&mut self, term: &Term) -> Stoppable<Option<Arc<Reading>>> {
        self.node(term, 0)
    }

    fn node(&mut self, term: &Term, depth: usize) -> Stoppable<Option<Arc<Reading>>> {
        stop::check()?;
        if let Some(result) = self.memo.get(term) {
            return Ok(result.clone());
        }
        if self.remaining == 0 || depth >= 128 {
            return Ok(None);
        }
        self.remaining -= 1;
        if !self.pure(term)? {
            return Ok(None);
        }
        let mut result = self
            .stored_reconstruction(term)
            .map(|value| Arc::new(Reading::Leaf(value)));
        if let TermKind::Application {
            symbol, arguments, ..
        } = term.kind()
        {
            let observation = match (symbol.attributes.hook.as_deref(), arguments.as_slice()) {
                (Some("MAP.lookup"), [map, key]) => Some((map, key, false)),
                (Some("MAP.in_keys"), [key, map]) => Some((map, key, true)),
                _ => None,
            };
            if let Some((map, key, presence)) = observation
                && let Some(ops) = self.definition.map_operations(&map.sort())
                && ops.admits(
                    term,
                    if presence {
                        "MAP.in_keys"
                    } else {
                        "MAP.lookup"
                    },
                )
                && (!presence
                    || self.definition.domain_kind(&term.sort())
                        == Some(crate::term::DomainKind::Bool))
                && (presence || term.sort() == ops.collection.value_sort)
                && let Some(key) = maps::read_at(self.definition, key, &ops.collection.key_sort)
            {
                let views = self
                    .maps
                    .entry(map.sort())
                    .or_insert_with(|| Views::new(self.definition, ops));
                if let Some(view) = views.of_pure(map)? {
                    let reading = self.observe(&view, &key, presence, term, depth + 1)?;
                    // A base observation is already the ordinary source function.
                    result = reading
                        .filter(|r| !matches!(r.as_ref(), Reading::Leaf(leaf) if leaf == term));
                }
            }
        }
        // Lift only checked selectors and free wrappers. Other pure functions compose
        // through their existing congruence, without distributing an entire expression.
        if result.is_none() && self.wrapper(term) {
            let mut selected = None;
            for child in crate::deferred::children(term) {
                if let Some(plan) = self.node(child, depth + 1)? {
                    if selected.as_ref().is_some_and(|(old, _)| old != child) {
                        selected = None;
                        break;
                    }
                    selected = Some((child.clone(), plan));
                }
            }
            if let Some((child, plan)) = selected {
                result = self.lift(term, &child, &plan, depth + 1)?;
            }
        }
        self.memo.insert(term.clone(), result.clone());
        Ok(result)
    }

    fn pure(&mut self, root: &Term) -> Stoppable<bool> {
        let Some(effects) = &self.effects else {
            return Ok(false);
        };
        let mut pending = vec![(root.clone(), false)];
        while let Some((term, visited)) = pending.pop() {
            stop::check()?;
            if self.pure.contains_key(&term) {
                continue;
            }
            if self.remaining == 0 {
                return Ok(false);
            }
            self.remaining -= 1;
            let local = crate::rewrite::functional_pattern_node(&term)
                && match term.kind() {
                    TermKind::Application { symbol, .. } => {
                        !symbol.attributes.binder
                            && !symbol.attributes.macro_or_alias
                            && !effects.contains(symbol.name.as_ref())
                    }
                    _ => true,
                };
            if !local {
                self.pure.insert(term, false);
                continue;
            }
            let children = crate::deferred::children(&term);
            if children.len() > self.remaining {
                return Ok(false);
            }
            if visited || children.is_empty() {
                let pure = children
                    .iter()
                    .all(|child| self.pure.get(*child) == Some(&true));
                self.pure.insert(term, pure);
            } else {
                pending.push((term.clone(), true));
                pending.extend(children.into_iter().map(|child| (child.clone(), false)));
            }
        }
        Ok(self.pure.get(root) == Some(&true))
    }

    fn wrapper(&self, term: &Term) -> bool {
        match term.kind() {
            TermKind::Injection { source, target, .. } => {
                self.definition.sort_graph().check_subsort(source, target) == Ok(true)
            }
            TermKind::Application {
                symbol, arguments, ..
            } => {
                symbol.attributes.head_role() == HeadRole::FreeConstructor
                    || matches!(arguments.as_slice(), [input]
                        if self.definition.selector(&input.sort(), &term.sort())
                            .and_then(|s| s.project(input.clone())).as_ref() == Some(term))
            }
            _ => false,
        }
    }

    fn stored_reconstruction(&self, term: &Term) -> Option<Term> {
        let TermKind::Injection {
            term: projected, ..
        } = term.kind()
        else {
            return None;
        };
        let TermKind::Application { arguments, .. } = projected.kind() else {
            return None;
        };
        let [input] = arguments.as_slice() else {
            return None;
        };
        self.definition
            .selector(&input.sort(), &projected.sort())?
            .reconstruct_subterm(self.definition, projected, term)
    }

    fn lift(
        &mut self,
        context: &Term,
        child: &Term,
        reading: &Arc<Reading>,
        depth: usize,
    ) -> Stoppable<Option<Arc<Reading>>> {
        stop::check()?;
        if self.remaining == 0 || depth >= 128 {
            return Ok(None);
        }
        self.remaining -= 1;
        Ok(Some(match reading.as_ref() {
            Reading::Missing => Arc::new(Reading::Missing),
            Reading::Leaf(value) => {
                let rebuilt = context
                    .try_map_children::<std::convert::Infallible>(|c| {
                        Ok(if c == child { value.clone() } else { c.clone() })
                    })
                    .unwrap();
                let value = match rebuilt.kind() {
                    TermKind::Application { arguments, .. } => match arguments.as_slice() {
                        [input] => self
                            .definition
                            .selector(&input.sort(), &rebuilt.sort())
                            .filter(|s| s.project(input.clone()).as_ref() == Some(&rebuilt))
                            .and_then(|s| s.value_in(self.definition, input))
                            .unwrap_or(rebuilt),
                        _ => rebuilt,
                    },
                    _ => rebuilt,
                };
                Arc::new(Reading::Leaf(value))
            }
            Reading::If { test, yes, no } => {
                let Some(yes) = self.lift(context, child, yes, depth + 1)? else {
                    return Ok(None);
                };
                let Some(no) = self.lift(context, child, no, depth + 1)? else {
                    return Ok(None);
                };
                choice(test.clone(), yes, no)
            }
        }))
    }

    fn observe(
        &mut self,
        view: &Arc<View>,
        key: &Term,
        presence: bool,
        source: &Term,
        depth: usize,
    ) -> Stoppable<Option<Arc<Reading>>> {
        stop::check()?;
        let request = (Arc::as_ptr(view) as usize, source.clone());
        if let Some(reading) = self.observations.get(&request) {
            return Ok(Some(reading.clone()));
        }
        if self.remaining == 0 || depth >= 128 {
            return Ok(None);
        }
        self.remaining -= 1;
        let reading = match view.as_ref() {
            View::Base(base) => {
                if matches!(base.kind(), TermKind::Map { entries, rest: None, .. } if entries.is_empty())
                {
                    Arc::new(if presence {
                        Reading::Leaf(Term::bool(false))
                    } else {
                        Reading::Missing
                    })
                } else {
                    let ops = self
                        .definition
                        .map_operations(&base.sort())
                        .expect("view operations");
                    let source = ops.on_base(source, base.clone());
                    let Some(source) = source else {
                        return Ok(None);
                    };
                    Arc::new(Reading::Leaf(source))
                }
            }
            View::Put {
                base,
                key: written,
                value,
            } => {
                let test = key_equal(self.definition, key, written);
                let yes = Arc::new(Reading::Leaf(if presence {
                    Term::bool(true)
                } else {
                    value.clone()
                }));
                if test == Predicate::True {
                    yes
                } else {
                    let Some(no) = self.observe(base, key, presence, source, depth + 1)? else {
                        return Ok(None);
                    };
                    choice(test, yes, no)
                }
            }
            View::Remove { base, key: removed } => {
                let test = key_equal(self.definition, key, removed);
                let yes = Arc::new(if presence {
                    Reading::Leaf(Term::bool(false))
                } else {
                    Reading::Missing
                });
                if test == Predicate::True {
                    yes
                } else {
                    let Some(no) = self.observe(base, key, presence, source, depth + 1)? else {
                        return Ok(None);
                    };
                    choice(test, yes, no)
                }
            }
            View::If { test, yes, no } => {
                let Some(yes) = self.observe(yes, key, presence, source, depth + 1)? else {
                    return Ok(None);
                };
                let Some(no) = self.observe(no, key, presence, source, depth + 1)? else {
                    return Ok(None);
                };
                choice(Predicate::Term(test.clone()), yes, no)
            }
        };
        self.observations.insert(request, reading.clone());
        Ok(Some(reading))
    }
}
