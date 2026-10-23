//! Data terms: ground terms whose meaning in a definition is fixed by its constructors and its
//! overload lowering alone, so that two different data terms denote different values of the
//! definition. A client comparing ends of two definitions (a differential test) compares only
//! terms that are data in both, each judged by its own definition.
//!
//! # The class
//!
//! An overload family is *broken* when the load-time critical-pair check taints one of the
//! indexes its overload equations are rooted at, or when it violates a premise of that check,
//! which the load only reports (an overload equation of another shape than the canonical one
//! below, as an overload placed across `K` has, or two members without a unique least common
//! overload; `confluence::ViolationKind::{OverloadShape, NoLeastCommonOverload}`). Its *members*
//! are *refused*: for a tainted index, the two symbols of each overload equation rooted there;
//! for a premise violation, every member of the family, closed over its overload pairs. A ground
//! term is *data* in a definition when it holds no refused symbol and is built only from
//!
//! - domain values, sort injections and free-constructor applications ([`HeadRole::FreeConstructor`]);
//! - map, list and set terms without an opaque rest, whose keys, values or elements are data and
//!   whose map keys and set elements are pairwise distinct;
//! - applications of an *overload data head* ([`DataHeads`]) that are instance-normal
//!   (`BackendDefinition::instance_normal`: no equation offered the application, from the
//!   definition's own equations, with its own subsort order, can apply to it), whose arguments
//!   are data. An overload data head `g` is an `anywhere` production that is not a declared
//!   function, has no hook, roots no `simplification` lemma, is not refused, and roots at least
//!   one executable equation, every one of which is a *canonical* overload equation of `g`:
//!   `g(p1, ..., pn) = inj{R,T}(h(x1, ..., xn))` (or `h(x1, ..., xn)`) with each `pi` the
//!   variable `xi` or `inj{Si,Ti}(xi)`, the variables distinct, `h` its overload partner
//!   (`RuleAttributes::overload`), and no `requires` or `ensures`; and the check leaves `g`'s
//!   index untainted (`confluence::ValueClaims::admit`).
//!
//! # What a data term denotes, and why two of them differ
//!
//! A term denotes a value of the initial model of the definition: two ground terms denote one
//! value exactly when every model of the definition equates them. Differing in *every* model is
//! not attainable for an overload application, since outside the instances of its equations a
//! model may interpret an equation head as it likes. The argument assumes:
//!
//! - **A1 (termination).** Evaluation terminates, as every evaluation assumes.
//! - **A2 (consistency).** The definition has a model in which the declarations the backend
//!   reads as true hold (`docs/compatibility.md`, "Anywhere rules", and the verdict contract of
//!   `confluence::CheckScope::All`): free constructors have no confusion and are injective; sort
//!   injections compose, are injective and differ from the constructors of their target sort.
//! - **A3 (no stray identification).** No equation outside an overload family equates two
//!   different ground terms of the constructor fragment (free constructors, domain values,
//!   injections, collections). An equation that did would be a definition error: a pair the
//!   check classifies is then reported as not joined, and one it does not classify (function
//!   equations whose closure reaches no equation head or overloaded symbol) is reported by
//!   `CheckScope::All`, which the load does not run.
//!
//! Then two different data terms of one definition differ in its initial model:
//!
//! 1. *The constructor fragment.* An overload family is the one place where K means equations
//!    between different productions' values: its axioms say its members are one operation. An
//!    unbroken family lowers every application to one normal form (stage 1 of the check: its
//!    canonical equations' pairs join, which is a complete test for that shape, and lowering
//!    terminates because each step replaces a production by a strictly lesser one of a finite
//!    family), so it equates no two different terms of the fragment. A broken family may: in the
//!    diamond `Bot < Id, Val`, `Ids` and `Vals` both `overload(Exps)` over the common `Bots`,
//!    the axioms give `inj{Ids,Exps}(.Ids) = .Exps = inj{Vals,Exps}(.Vals)`. An overload axiom's
//!    two sides differ only at their roots, which are members, so no term free of the refused
//!    members is an instance of either side. With A2 and A3, two different terms of the fragment
//!    are then kept apart by some model.
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
//! # Two definitions
//!
//! A differential test asks whether the mutant's end `tm` is none of the baseline's ends `tb`.
//! Each definition reads the ends with its own theory, and the two theories may differ on any
//! symbol: a constructor free in one may be an overload head of the other (a mutant that adds
//! `Bot ::= f(Bot) [overload(f)]` lowers the baseline's normal form `f_Nm(inj(b))` to
//! `inj(f_Bot(b))`), an `anywhere` rule may be added (`c(1) => d`), a subsort may be added below
//! an overload argument sort, parametric instances such as `MInt{8}` included. So the comparison
//! is sound when every term compared is data in *both* definitions, each judged by
//! [`BackendDefinition::is_data`] with that definition's own [`DataHeads`] (its own families,
//! taint and equations, its own full subsort order through its matcher). Then, by the argument
//! above under A1 to A3 for each definition, two different such terms denote different values of
//! each definition's initial model, so `tm` differs from every `tb` whichever theory reads them.
//! Syntactic difference is read on k-rust's internal normal form, whose injections are taken
//! from the term's own sort (nested injections compose), which does not depend on the
//! definition. A term that does not internalize in a definition (a symbol it lacks) is not data
//! there.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    definition::BackendDefinition,
    rule::{RuleRhs, TermIndex},
    term::{HeadRole, Name, Term, TermKind},
};

/// The overload data heads and the refused symbols of one definition (the
/// [module documentation](self), "The class"), built by [`BackendDefinition::data_heads`] and
/// read only by [`BackendDefinition::is_data`] of the same definition.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DataHeads {
    heads: BTreeSet<Name>,
    /// The members of the definition's broken overload families: no term that holds one is
    /// data.
    refused: BTreeSet<Name>,
}

impl DataHeads {
    /// The refused symbols, sorted: no term that holds one is data.
    pub fn refused(&self) -> impl Iterator<Item = &Name> {
        self.refused.iter()
    }

    /// The heads' symbol names, sorted.
    pub fn names(&self) -> impl Iterator<Item = &Name> {
        self.heads.iter()
    }

    /// Whether `name` is one of the heads.
    #[must_use]
    pub fn contains(&self, name: &Name) -> bool {
        self.heads.contains(name)
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
        let refused = self.broken_family_members();
        let mut heads = BTreeSet::new();
        for (name, symbol) in self.symbols() {
            if refused.contains(name)
                || symbol.attributes.head_role() != HeadRole::EquationHead
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
            let mut rules = groups.values().flatten().peekable();
            let overload_only = rules.peek().is_some()
                && rules.all(|rule| {
                    rule.attributes.executable && canonical_overload_equation(name, rule)
                });
            if overload_only {
                heads.insert(name.clone());
            }
        }
        DataHeads { heads, refused }
    }

    /// The members of the broken overload families: the two symbols of every overload equation
    /// rooted at an index the load-time check taints, and every member of a family whose
    /// overload equations break a premise of the check, which the load only reports (an
    /// equation of another shape, two members without a unique least common overload:
    /// `ViolationKind::OverloadShape`, `NoLeastCommonOverload`). An overload axiom's two sides
    /// differ only at their roots, both members, so these cover every pair of different terms
    /// such a family's axioms equate.
    fn broken_family_members(&self) -> BTreeSet<Name> {
        use crate::confluence::ViolationKind;
        let overload_pairs = || {
            self.function_theory()
                .values()
                .flat_map(BTreeMap::values)
                .flatten()
                .filter_map(|rule| rule.attributes.overload.as_ref())
        };
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
            for (greater, lesser) in overload_pairs() {
                if family.contains(greater) || family.contains(lesser) {
                    family.insert(greater.clone());
                    family.insert(lesser.clone());
                }
            }
            if family.len() == before {
                break;
            }
        }
        for (index, groups) in self.function_theory() {
            if !matches!(index, TermIndex::Symbol(_)) || self.value_claims().admit(index).is_some()
            {
                continue;
            }
            for (greater, lesser) in groups
                .values()
                .flatten()
                .filter_map(|rule| rule.attributes.overload.as_ref())
            {
                family.insert(greater.clone());
                family.insert(lesser.clone());
            }
        }
        family
    }

    /// Whether the ground term `term` is data in this definition (the
    /// [module documentation](self)), with the applications of the heads in `heads` admitted
    /// where they are instance-normal. `heads` must come from [`Self::data_heads`] of this
    /// definition. Ends compared across two definitions must be data in both, each judged by its
    /// own definition ("Two definitions").
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
