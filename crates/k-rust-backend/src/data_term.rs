//! Data terms: ground terms whose meaning is fixed by constructors and overload lowering alone,
//! so that two different data terms denote different values and a data term denotes the same
//! value in two definitions that agree on the overload equations it relies on.
//!
//! A ground term is *data* in a definition when it is built only from
//!
//! - domain values, sort injections and free-constructor applications ([`HeadRole::FreeConstructor`]);
//! - map, list and set terms without an opaque rest, whose keys, values or elements are data and
//!   whose map keys and set elements are pairwise distinct;
//! - applications of an *overload data head* ([`DataHeads`]) that are instance-normal
//!   (`BackendDefinition::instance_normal`: no equation offered the application can apply to
//!   it), whose arguments are data.
//!
//! The first two cases are the terms the backend calls constructor-like
//! ([`crate::term::TermAttributes::constructor_like`]): the constructor and no-confusion axioms
//! make two different such terms different in every model. The third case needs the argument
//! below.
//!
//! # Why an irreducible overload application is data
//!
//! An overload data head `g` is an `anywhere` production that is not a declared function, has no
//! hook, roots no `simplification` lemma, and whose executable equations are all overload
//! equations rooted at `g` (`RuleAttributes::overload`, generated from the `overload` attribute):
//! `g(inj{S1,T1}(K1), ..., inj{Sn,Tn}(Kn)) = inj{R,T}(h(K1, ..., Kn))` with `h` a lesser production
//! of the family. The load-time check must leave `g`'s index untainted
//! (`confluence::ValueClaims::admit`).
//!
//! The backend reads a definition with equations by its normal-form model `M_NF`
//! (`docs/compatibility.md`, "Anywhere rules"): each sort is interpreted by the normal forms of
//! innermost evaluation and each symbol by normalizing its application. `M_NF` is a model of the
//! definition when evaluation terminates (the assumption every evaluation makes) and the
//! critical pairs of the executable equations join, which the load checks; a pair that does not
//! join taints, through a closure, every equation head and overloaded symbol whose claims it
//! could falsify. In `M_NF` distinct normal forms are distinct elements. So when `g` is
//! untainted, an application of `g` that no equation reaches and whose arguments are normal forms
//! is an element of `M_NF` distinct from every other normal form. Ground terms are equal in the
//! initial model of the definition only when every model of the definition equates them; `M_NF`
//! is a model that does not, so two different data terms are different in the initial model,
//! which is what a comparison of ends needs.
//!
//! The restriction to overload-only heads is what makes the judgement depend on no evaluation
//! the run does not show: overload lowering terminates (each step replaces a head by a strictly
//! lesser production of a finite family), its equations have no condition, and their left-hand
//! sides hold only injections of variables, so whether one applies reads only the arguments'
//! injection sorts and the subsort order. A head with any other equation, or a lemma that could
//! identify its applications with other values, is refused. The vacuous case of an equation head
//! with no equation at all is refused too: nothing in the definition makes it a head of the data
//! fragment.
//!
//! # Two definitions
//!
//! A data term denotes itself in each definition. It denotes the *same* value in two
//! definitions only where both give its overload heads the same equations and the same subsort
//! order below the equations' argument sorts: then irreducibility in one is irreducibility in the
//! other, and the fragment of constructors and overload families the term lives in is the same
//! theory in both. [`DataHeads::agreeing_with`] keeps exactly the heads for which that holds;
//! a client comparing ends across two definitions judges both sides' ends against the agreeing
//! heads.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    condition::Condition,
    definition::BackendDefinition,
    rule::{RuleRhs, TermIndex},
    term::{HeadRole, Name, Sort, Term, TermKind},
};

/// The overload data heads of a definition (the [module documentation](self)), each with the
/// facts two definitions must share for its applications to mean the same in both. Built by
/// [`BackendDefinition::data_heads`], narrowed by [`Self::agreeing_with`].
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DataHeads {
    heads: BTreeMap<Name, HeadFacts>,
}

/// What an overload data head's applications read: its equations, and for each sort an equation
/// argument injects from, the sorts below it, which decide whether that argument matches.
#[derive(Clone, Debug, Eq, PartialEq)]
struct HeadFacts {
    equations: Vec<OverloadEquation>,
    below: BTreeMap<Sort, BTreeSet<Name>>,
}

/// One overload equation as the evaluator applies it.
#[derive(Clone, Debug, Eq, PartialEq)]
struct OverloadEquation {
    priority: u8,
    lhs: Term,
    rhs: RuleRhs,
    requires: Condition,
    ensures: Condition,
}

impl DataHeads {
    /// The heads of `self` that `other` also has, with equal equations and equal subsort facts:
    /// the heads whose applications denote the same value in both definitions.
    #[must_use]
    pub fn agreeing_with(&self, other: &DataHeads) -> DataHeads {
        DataHeads {
            heads: self
                .heads
                .iter()
                .filter(|(name, facts)| other.heads.get(*name) == Some(facts))
                .map(|(name, facts)| (name.clone(), facts.clone()))
                .collect(),
        }
    }

    /// The heads' symbol names, sorted.
    pub fn names(&self) -> impl Iterator<Item = &Name> {
        self.heads.keys()
    }

    /// Whether `name` is one of the heads.
    #[must_use]
    pub fn contains(&self, name: &Name) -> bool {
        self.heads.contains_key(name)
    }

    /// Whether there is no head.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.heads.is_empty()
    }
}

impl BackendDefinition {
    /// The overload data heads of this definition (the [module documentation](self)): every
    /// `anywhere` production that is not a declared function, has no hook, roots no
    /// simplification, roots at least one executable equation and only overload equations rooted
    /// at itself, and whose index the load-time critical-pair check leaves untainted.
    #[must_use]
    pub fn data_heads(&self) -> DataHeads {
        let mut heads = BTreeMap::new();
        for (name, symbol) in self.symbols() {
            if symbol.attributes.head_role() != HeadRole::EquationHead
                || symbol.attributes.hook.is_some()
            {
                continue;
            }
            let index = TermIndex::Symbol(name.clone());
            if self.simplification_theory().contains_key(&index)
                || self.value_claims().admit(&index).is_none()
            {
                continue;
            }
            let Some(groups) = self.function_theory().get(&index) else {
                continue;
            };
            let mut equations = Vec::new();
            let mut only_overloads = true;
            for (priority, rules) in groups {
                for rule in rules {
                    let rooted_overload = rule
                        .attributes
                        .overload
                        .as_ref()
                        .is_some_and(|(greater, _)| greater == name);
                    if !rooted_overload || !rule.attributes.executable {
                        only_overloads = false;
                    }
                    equations.push(OverloadEquation {
                        priority: *priority,
                        lhs: rule.lhs.clone(),
                        rhs: rule.rhs.clone(),
                        requires: rule.requires.clone(),
                        ensures: rule.ensures.clone(),
                    });
                }
            }
            if !only_overloads || equations.is_empty() {
                continue;
            }
            let below = self.sorts_below_injections(&equations);
            heads.insert(name.clone(), HeadFacts { equations, below });
        }
        DataHeads { heads }
    }

    /// For each sort an argument of an equation's left-hand side injects from, the nullary sorts
    /// of this definition below it (itself included).
    fn sorts_below_injections(
        &self,
        equations: &[OverloadEquation],
    ) -> BTreeMap<Sort, BTreeSet<Name>> {
        let mut below = BTreeMap::new();
        for equation in equations {
            let TermKind::Application { arguments, .. } = equation.lhs.kind() else {
                continue;
            };
            for argument in arguments {
                let TermKind::Injection { source, .. } = argument.kind() else {
                    continue;
                };
                below.entry(*source).or_insert_with(|| {
                    self.sorts()
                        .iter()
                        .filter(|(_, info)| info.parameters.is_empty())
                        .filter(|(sub, _)| {
                            self.sort_graph()
                                .check_subsort(&Sort::simple((*sub).clone()), source)
                                .unwrap_or(false)
                        })
                        .map(|(sub, _)| sub.clone())
                        .collect()
                });
            }
        }
        below
    }

    /// Whether the ground term `term` is data (the [module documentation](self)), with the
    /// applications of the heads in `heads` admitted where they are instance-normal. `heads` must
    /// come from [`Self::data_heads`] of this definition, possibly narrowed by
    /// [`DataHeads::agreeing_with`]. A constructor-like term is data whatever `heads` holds.
    #[must_use]
    pub fn is_data(&self, term: &Term, heads: &DataHeads) -> bool {
        crate::instance_normal::with_scan_memo(|| self.is_data_walk(term, heads))
    }

    fn is_data_walk(&self, term: &Term, heads: &DataHeads) -> bool {
        let mut pending = vec![term];
        // Invariant: every term popped is a subterm of `term`, and each subterm is pushed once by
        // its parent, so the loop visits at most the nodes of `term`.
        while let Some(term) = pending.pop() {
            if term.attributes().constructor_like {
                continue;
            }
            match term.kind() {
                TermKind::DomainValue { .. } => {}
                TermKind::Injection { term, .. } => pending.push(term),
                TermKind::Application {
                    symbol, arguments, ..
                } => match symbol.attributes.head_role() {
                    HeadRole::FreeConstructor => pending.extend(arguments),
                    HeadRole::EquationHead
                        if heads.contains(&symbol.name) && self.instance_normal(term).is_some() =>
                    {
                        pending.extend(arguments);
                    }
                    HeadRole::EquationHead
                    | HeadRole::Function { .. }
                    | HeadRole::Uninterpreted
                    | HeadRole::Residual => return false,
                },
                TermKind::Map { entries, rest, .. } => {
                    if rest.is_some() {
                        return false;
                    }
                    let mut previous: Option<&Term> = None;
                    for (key, value) in entries {
                        // Entries are sorted by key, so a key bound twice follows its first binding.
                        if previous == Some(key) {
                            return false;
                        }
                        previous = Some(key);
                        pending.push(key);
                        pending.push(value);
                    }
                }
                TermKind::List {
                    heads: items, rest, ..
                } => {
                    if rest.is_some() {
                        return false;
                    }
                    pending.extend(items);
                }
                TermKind::Set { elements, rest, .. } => {
                    if rest.is_some() {
                        return false;
                    }
                    let mut previous: Option<&Term> = None;
                    for element in elements {
                        if previous == Some(element) {
                            return false;
                        }
                        previous = Some(element);
                        pending.push(element);
                    }
                }
                TermKind::Variable(_) | TermKind::And(..) => return false,
            }
        }
        true
    }
}
