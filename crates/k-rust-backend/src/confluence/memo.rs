//! The check's memo of condition simplifications, keyed up to a renaming of free variables.
//!
//! Within one check the simplifier's other inputs are fixed: the definition, which withholds
//! every claim while the check runs, the options (`CONDITION_ITERATIONS`, no assumption) and the
//! solver (`NoSolver`). So an answer is a function of the predicate, and since every
//! simplification step is an axiom instance, which holds under any injective renaming of the
//! predicate's free variables, an answer for one predicate renamed back is an answer for every
//! predicate that renames to it. Many pairs instantiate the same `requires` with differently
//! named variables, so the key is the predicate with its free variables renamed to
//! `Var!memo{i}` in order of first occurrence, each keeping its sort and kind.
//!
//! Three cases keep a renaming from capturing or conflating anything:
//!
//! - a predicate with a quantifier is keyed as written: renaming its free variables could make
//!   one of them meet a bound name;
//! - an answer is stored only when its free variables are among the key's, so that renaming it
//!   back is defined on all of them and two answers never share a variable the simplifier
//!   introduced;
//! - an answer with a quantifier is stored only under a key as written, so that renaming it back
//!   cannot bring a free variable under a binder of the same name.
//!
//! An answer either case keeps out is *refused*: the predicate as written is simplified instead,
//! and the key is marked refused. Whether a key's answer is refused is a function of the key
//! (both cases read only the answer, the key's free variables and whether the key has a renaming
//! back, which it lacks exactly when it has a quantifier or no free variable), so every later
//! predicate with that key is simplified as written directly, and a key is simplified at most
//! once per check.
//!
//! A stopped or failed simplification is stored as "decides nothing", which is what the check
//! reads it as wherever it occurs.

use std::collections::BTreeMap;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    rule::{Predicate, rename_predicates},
    stop::PollBudgetRecord,
    term::{
        Term, TermKind, Variable, VariableKind,
        names::{FreshMarker, with_fresh_marker},
    },
};

/// Stored answers, by canonical predicate.
#[derive(Default)]
pub(super) struct Memo {
    answers: FxHashMap<Predicate, Stored>,
}

/// What the memo holds for a key.
enum Stored {
    /// The key's answer, `None` for "decides nothing", and the stops its simplification met.
    Answer(Option<Predicate>, PollBudgetRecord),
    /// The key's answer could not be renamed back.
    Refused,
}

/// A predicate in the memo's canonical form, with the renaming back to the original's names.
pub(super) struct Canonical {
    pub(super) key: Predicate,
    /// Canonical name to original variable; empty exactly when the predicate has a quantifier
    /// (it is keyed as written) or no free variable.
    back: BTreeMap<Variable, Variable>,
}

/// What the memo says about a predicate.
pub(super) enum Lookup {
    /// The stored answer, renamed back to the predicate's names, and the stops its
    /// simplification met.
    Hit(Option<Predicate>, PollBudgetRecord),
    /// The key's answer was refused earlier in the check: simplify the predicate as written,
    /// and store nothing.
    AsWritten,
    /// No answer stored: simplify [`Canonical::key`] and hand the answer to
    /// [`Memo::store`].
    Miss(Canonical),
}

impl Memo {
    pub(super) fn lookup(&self, predicate: &Predicate) -> Lookup {
        let canonical = Canonical::of(predicate);
        match self.answers.get(&canonical.key) {
            Some(Stored::Answer(answer, stops)) => {
                Lookup::Hit(answer.as_ref().map(|answer| canonical.back(answer)), *stops)
            }
            Some(Stored::Refused) => Lookup::AsWritten,
            None => Lookup::Miss(canonical),
        }
    }

    /// Store `answer`, the simplification of `canonical.key`, with the stops it met, when it may
    /// be renamed back, and return it renamed back; when it may not be, mark the key refused and
    /// return `Err(())`: the caller must simplify the predicate as written.
    pub(super) fn store(
        &mut self,
        canonical: Canonical,
        answer: Option<Predicate>,
        stops: PollBudgetRecord,
    ) -> Result<Option<Predicate>, ()> {
        if let Some(answer) = &answer {
            let key_variables = canonical.key.free_variables();
            if !answer.free_variables().is_subset(&key_variables)
                || (!canonical.back.is_empty() && has_binder(answer))
            {
                self.answers.insert(canonical.key, Stored::Refused);
                return Err(());
            }
        }
        let renamed = answer.as_ref().map(|answer| canonical.back(answer));
        self.answers
            .insert(canonical.key, Stored::Answer(answer, stops));
        Ok(renamed)
    }
}

impl Canonical {
    pub(super) fn of(predicate: &Predicate) -> Self {
        if has_binder(predicate) {
            return Self {
                key: predicate.clone(),
                back: BTreeMap::new(),
            };
        }
        let mut order = Vec::new();
        let mut seen = FxHashSet::default();
        predicate.visit_terms(&mut |term| first_occurrences(term, &mut seen, &mut order));
        let forward = order
            .into_iter()
            .enumerate()
            .map(|(index, variable)| {
                let base = match variable.kind {
                    VariableKind::Element => "Var",
                    VariableKind::Set => "@Var",
                };
                let name = with_fresh_marker(base, FreshMarker::Memo, index as u64);
                let canonical = variable.with_name(name);
                (variable, canonical)
            })
            .collect::<BTreeMap<_, _>>();
        let key = rename(predicate, &forward);
        let back = forward
            .into_iter()
            .map(|(original, canonical)| (canonical, original))
            .collect();
        Self { key, back }
    }

    fn back(&self, answer: &Predicate) -> Predicate {
        if self.back.is_empty() {
            answer.clone()
        } else {
            rename(answer, &self.back)
        }
    }
}

fn rename(predicate: &Predicate, renaming: &BTreeMap<Variable, Variable>) -> Predicate {
    let rename = |variable: &Variable| {
        renaming
            .get(variable)
            .cloned()
            .unwrap_or_else(|| variable.clone())
    };
    rename_predicates(std::slice::from_ref(predicate), rename)
        .pop()
        .expect("one predicate renamed")
}

/// The variables of `term` not in `seen`, appended to `order` left to right, depth first.
pub(super) fn first_occurrences(
    term: &Term,
    seen: &mut FxHashSet<Variable>,
    order: &mut Vec<Variable>,
) {
    if term
        .attributes()
        .variables
        .iter()
        .all(|variable| seen.contains(variable))
    {
        return;
    }
    match term.kind() {
        TermKind::Variable(variable) => {
            seen.insert(variable.clone());
            order.push(variable.clone());
        }
        TermKind::DomainValue { .. } => {}
        TermKind::And(left, right) => {
            first_occurrences(left, seen, order);
            first_occurrences(right, seen, order);
        }
        TermKind::Application { arguments, .. } => {
            for argument in arguments {
                first_occurrences(argument, seen, order);
            }
        }
        TermKind::Injection { term, .. } => first_occurrences(term, seen, order),
        TermKind::Map { entries, rest, .. } => {
            for (key, value) in entries {
                first_occurrences(key, seen, order);
                first_occurrences(value, seen, order);
            }
            if let Some(rest) = rest {
                first_occurrences(rest, seen, order);
            }
        }
        TermKind::List { heads, rest, .. } => {
            for head in heads {
                first_occurrences(head, seen, order);
            }
            if let Some((middle, tails)) = rest {
                first_occurrences(middle, seen, order);
                for tail in tails {
                    first_occurrences(tail, seen, order);
                }
            }
        }
        TermKind::Set { elements, rest, .. } => {
            for element in elements {
                first_occurrences(element, seen, order);
            }
            if let Some(rest) = rest {
                first_occurrences(rest, seen, order);
            }
        }
    }
}

/// Whether `predicate` has a quantifier.
fn has_binder(predicate: &Predicate) -> bool {
    match predicate {
        Predicate::Exists(..) | Predicate::Forall(..) => true,
        Predicate::True
        | Predicate::False
        | Predicate::Term(_)
        | Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Defined(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Absent(_) => false,
        Predicate::Not(inner) => has_binder(inner),
        Predicate::And(inner) | Predicate::Or(inner) => inner.iter().any(has_binder),
        Predicate::Implies(left, right) | Predicate::Iff(left, right) => {
            has_binder(left) || has_binder(right)
        }
    }
}
