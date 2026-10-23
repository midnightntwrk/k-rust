//! Data terms: ground terms whose meaning is fixed by constructors and overload lowering alone,
//! so that two different data terms denote different values and a data term denotes the same
//! value in two definitions that agree on the overload equations it relies on.
//!
//! # The class
//!
//! Call a symbol *refused* when an overload equation rooted at a member of a *broken* overload
//! family mentions it: a family one of whose members' index the load-time critical-pair check
//! taints, or one that violates a premise of that check, which the load only reports (an
//! overload equation of another shape than `g(inj(x1), ..., inj(xn)) = inj(h(x1, ..., xn))`, as
//! an overload placed across `K` has, or two members without a unique least common overload;
//! `confluence::ViolationKind::{OverloadShape, NoLeastCommonOverload}`). A ground term is *data*
//! in a definition when it holds no refused symbol and is built only from
//!
//! - domain values, sort injections and free-constructor applications ([`HeadRole::FreeConstructor`]);
//! - map, list and set terms without an opaque rest, whose keys, values or elements are data and
//!   whose map keys and set elements are pairwise distinct;
//! - applications of an *overload data head* ([`DataHeads`]) that are instance-normal
//!   (`BackendDefinition::instance_normal`: no equation offered the application can apply to
//!   it), whose arguments are data. An overload data head `g` is an `anywhere` production that is
//!   not a declared function, has no hook, roots no `simplification` lemma, is not refused, and
//!   roots at least one executable equation, every one of which is an overload equation of `g`
//!   (`RuleAttributes::overload`, generated from K's `overload` attribute) of the shape
//!   `g(p1, ..., pn) = inj{R,T}(h(x1, ..., xn))` (or `h(x1, ..., xn)`) with each `pi` the
//!   variable `xi` or `inj{Si,Ti}(xi)`, the variables distinct, `h` its overload partner, and no
//!   `requires` or `ensures`; and the check leaves `g`'s index untainted
//!   (`confluence::ValueClaims::admit`).
//!
//! # What a data term denotes, and why two of them differ
//!
//! A term denotes a value of the initial model of the definition, read as k-rust reads it
//! (`docs/compatibility.md`, "Anywhere rules", and the verdict contract of
//! `confluence::CheckScope::All`): its axioms together with the declarations the backend takes as
//! true, here that free constructors have no confusion and are injective, and that sort
//! injections compose, are injective and differ from a constructor of their target sort. Two
//! ground terms denote one value of the initial model exactly when every model equates them, so
//! two data terms differ there when one model keeps them apart. Differing in *every* model is not
//! attainable for an overload application: outside the instances of its equations a model may
//! interpret an equation head as it likes, two irreducible applications included. The initial
//! model is the meaning of a definition, and the ends a client compares are values of it.
//!
//! Termination of evaluation is assumed, as every evaluation assumes it. Suppose the definition
//! has a model (otherwise there is nothing to compare). Then:
//!
//! 1. *The constructor fragment.* Two different ground terms built from domain values, free
//!    constructors, canonical injections and well-formed collections are kept apart by the
//!    declarations above, except where the definition's own equations equate them. An overload
//!    family is the one place where K means equations between different productions' values:
//!    its axioms say its members are one operation. An unbroken family lowers every application
//!    to one normal form (stage 1 of the check: its overload equations' pairs join, which is a
//!    complete test for the canonical shape, and the lowering terminates because each step
//!    replaces a production by a strictly lesser one of a finite family), so it equates no two
//!    different terms of the fragment. A broken family may: in the diamond `Bot < Id, Val`,
//!    `Ids` and `Vals` both `overload(Exps)` over the common `Bots`, the axioms give
//!    `inj{Ids,Exps}(.Ids) = .Exps = inj{Vals,Exps}(.Vals)`. Its members and the constructors
//!    its equations lower to are therefore not read as free, and every term holding one is
//!    refused. Any other equation that equated two different terms of the fragment would deny a
//!    declaration the backend reads as true, and the definition would have no model.
//! 2. *Overload applications.* With its closure of the pairs that do not join, the check
//!    guarantees that, whenever the definition has a model, one model makes every claim on an
//!    untainted term true at once (compat, "Anywhere rules": it keeps the values of any model,
//!    adds the untainted equations' normal forms that hold an untainted equation-head
//!    application as new values, distinct from every other value, and no tainted equation can
//!    see a new value). Build it on a model of 1. An instance-normal application of an untainted
//!    overload data head over data is such a normal form. By induction on the first position
//!    where two different data terms differ, that model gives them different values: free
//!    constructors and injections are injective and have no confusion on old and new values
//!    alike, collections with distinct keys denote their finite maps and sets, and new values
//!    are distinct from every other value.
//!
//! So two different data terms differ in the initial model. The canonical shape matters twice:
//! stage 1 decides the family's confluence only for it, and whether such an equation applies
//! reads only each argument's injection source sort and the subsort order, which the next part
//! uses.
//!
//! # Two definitions
//!
//! A data term denotes itself in each definition. It denotes the *same* value in two
//! definitions only where the fragment it lives in is the same theory in both: both give each of
//! its overload heads the same canonical equations and the same subsorts below the sorts those
//! equations' arguments inject from (everything their matching reads), so irreducibility in one
//! is irreducibility in the other, and no symbol of it is refused in either.
//! [`DataHeads::agreeing_with`] keeps exactly those heads and unites the refused symbols; a
//! client comparing ends across two definitions judges both sides' ends against the result.

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
    /// The refused symbols (the [module documentation](self), "The class"): no term that holds
    /// one is data.
    refused: BTreeSet<Name>,
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
        let refused: BTreeSet<Name> = self.refused.union(&other.refused).cloned().collect();
        DataHeads {
            heads: self
                .heads
                .iter()
                .filter(|(name, facts)| {
                    other.heads.get(*name) == Some(facts) && !refused.contains(*name)
                })
                .map(|(name, facts)| (name.clone(), facts.clone()))
                .collect(),
            refused,
        }
    }

    /// The refused symbols of either definition, sorted: no term that holds one is data.
    pub fn refused(&self) -> impl Iterator<Item = &Name> {
        self.refused.iter()
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
    /// The overload data heads and the refused symbols of this definition (the
    /// [module documentation](self), "The class"): every `anywhere` production that is not a
    /// declared function, has no hook, roots no simplification, is not refused, roots at least
    /// one executable equation and only canonically shaped overload equations rooted at itself,
    /// and whose index the load-time critical-pair check leaves untainted.
    #[must_use]
    pub fn data_heads(&self) -> DataHeads {
        let refused = self.tainted_overload_symbols();
        let mut heads = BTreeMap::new();
        for (name, symbol) in self.symbols() {
            if refused.contains(name) {
                continue;
            }
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
                    if !rooted_overload
                        || !rule.attributes.executable
                        || !canonical_overload_equation(name, rule)
                    {
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
        DataHeads { heads, refused }
    }

    /// The symbols mentioned, on either side, by an overload equation rooted at a symbol whose
    /// index the load-time check taints, or of a family whose overload equations break a
    /// premise of the check (an equation of another shape, two members without a unique least
    /// common overload: `ViolationKind::OverloadShape`, `NoLeastCommonOverload`), which the load
    /// only reports.
    fn tainted_overload_symbols(&self) -> BTreeSet<Name> {
        use crate::confluence::ViolationKind;
        let overload_rules = || {
            self.function_theory()
                .values()
                .flat_map(BTreeMap::values)
                .flatten()
                .filter(|rule| rule.attributes.overload.is_some())
        };
        // The families whose premises fail: the named members, closed over the overload pairs.
        let mut family = BTreeSet::new();
        for violation in self.value_claims().violations() {
            match &violation.kind {
                ViolationKind::OverloadShape(name) => {
                    family.insert(name.clone());
                }
                ViolationKind::NoLeastCommonOverload(left, right) => {
                    family.insert(left.clone());
                    family.insert(right.clone());
                }
                ViolationKind::ConstructorHeaded(_)
                | ViolationKind::InjectionHeaded
                | ViolationKind::IndexedAt(_)
                | ViolationKind::PinnedByInjectiveTotal(_) => {}
            }
        }
        // Invariant: `family` only grows, bounded by the overloaded symbols.
        loop {
            let before = family.len();
            for rule in overload_rules() {
                if let Some((greater, lesser)) = &rule.attributes.overload
                    && (family.contains(greater) || family.contains(lesser))
                {
                    family.insert(greater.clone());
                    family.insert(lesser.clone());
                }
            }
            if family.len() == before {
                break;
            }
        }
        let mut refused = BTreeSet::new();
        for (index, groups) in self.function_theory() {
            let TermIndex::Symbol(root) = index else {
                continue;
            };
            if self.value_claims().admit(index).is_some() && !family.contains(root) {
                continue;
            }
            for rule in groups.values().flatten() {
                if rule.attributes.overload.is_none() {
                    continue;
                }
                let mut collect = |symbol: &crate::term::Symbol| {
                    refused.insert(symbol.name.clone());
                };
                rule.lhs.visit_symbols(&mut collect);
                if let RuleRhs::Term(rhs) = &rule.rhs {
                    rhs.visit_symbols(&mut collect);
                }
            }
        }
        refused
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
        // With a tainted overload family, constructor-like terms the family identifies are not
        // data, so every symbol is looked at.
        let shortcut = heads.refused.is_empty();
        while let Some(term) = pending.pop() {
            if shortcut && term.attributes().constructor_like {
                continue;
            }
            match term.kind() {
                TermKind::DomainValue { .. } => {}
                TermKind::Injection { term, .. } => pending.push(term),
                TermKind::Application { symbol, .. } if heads.refused.contains(&symbol.name) => {
                    return false;
                }
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

/// Whether `rule`, an overload equation rooted at `head`, has the shape the overload axioms of
/// a K `overload` family have and the argument of the [module documentation](self) covers:
/// `head(p1, ..., pn) = inj{R,T}(lesser(x1, ..., xn))` or `= lesser(x1, ..., xn)`, where each
/// `pi` is the variable `xi` or an injection `inj{Si,Ti}(xi)` of it, the variables pairwise
/// distinct, `lesser` the equation's overload partner, and no `requires` or `ensures`. Whether
/// such an equation applies reads only each argument's injection source sort and the subsort
/// order. Any other shape (an overload placed across `K`, whose argument is `kseq(inj(X),
/// dotk)`, which the load reports as a precondition violation) is not covered.
fn canonical_overload_equation(head: &Name, rule: &crate::rule::RewriteRule) -> bool {
    let Some((_, lesser)) = &rule.attributes.overload else {
        return false;
    };
    if !rule.requires.is_empty() || !rule.ensures.is_empty() {
        return false;
    }
    let TermKind::Application {
        symbol, arguments, ..
    } = rule.lhs.kind()
    else {
        return false;
    };
    if &symbol.name != head {
        return false;
    }
    let mut variables = Vec::new();
    for argument in arguments {
        let variable = match argument.kind() {
            TermKind::Variable(variable) => variable,
            TermKind::Injection { term, .. } => match term.kind() {
                TermKind::Variable(variable) => variable,
                _ => return false,
            },
            _ => return false,
        };
        if variables.contains(&variable) {
            return false;
        }
        variables.push(variable);
    }
    let RuleRhs::Term(rhs) = &rule.rhs else {
        return false;
    };
    let lowered = match rhs.kind() {
        TermKind::Injection { term, .. } => term,
        _ => rhs,
    };
    let TermKind::Application {
        symbol, arguments, ..
    } = lowered.kind()
    else {
        return false;
    };
    &symbol.name == lesser
        && arguments.len() == variables.len()
        && arguments
            .iter()
            .zip(&variables)
            .all(|(argument, variable)| {
                matches!(argument.kind(), TermKind::Variable(found) if found == *variable)
            })
}
