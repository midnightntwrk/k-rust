//! Data terms: ground terms whose meaning in a definition is fixed by its constructors and its
//! overload lowering alone, so that two different data terms denote different values of the
//! definition. A client comparing ends of two definitions (a differential test) compares only
//! terms that are data in both, each judged by its own definition.
//!
//! # The class
//!
//! A definition *has data* when its full critical-pair check
//! ([`CheckScope::All`](crate::confluence::CheckScope::All), which classifies every pair of
//! executable equations) reports nothing: every pair joins or is separated or refuted, no
//! equation is one the evaluator does not apply to every subject it describes, and no
//! precondition row is violated (no equation rooted at a free constructor, an injection, a
//! collection or a bare variable; every overload equation of the canonical shape below; a unique
//! least common overload for any two members of a family). A definition whose check reports
//! something has no data: its findings ([`DataHeads::findings`]) say why. In a definition that
//! has data, a ground term is *data* when it is built only from
//!
//! - domain values, sort injections and free-constructor applications ([`HeadRole::FreeConstructor`]);
//! - map, list and set terms without an opaque rest, whose keys, values or elements are data and
//!   whose map keys and set elements are pairwise distinct;
//! - applications of an *overload data head* ([`DataHeads`]) that are instance-normal
//!   (`BackendDefinition::instance_normal`: no equation offered the application, from the
//!   definition's own equations, with its own subsort order, can apply to it), whose arguments
//!   are data. An overload data head `g` is an `anywhere` production that is not a declared
//!   function, has no hook, roots no `simplification` lemma, and roots at least one executable
//!   equation, every one of which is a *canonical* overload equation of `g`:
//!   `g(p1, ..., pn) = inj{R,T}(h(x1, ..., xn))` (or `h(x1, ..., xn)`) with each `pi` the
//!   variable `xi` or `inj{Si,Ti}(xi)`, the variables distinct, `h` its overload partner
//!   (`RuleAttributes::overload`), and no `requires` or `ensures`.
//!
//! # What a data term denotes, and why two of them differ
//!
//! A term denotes a value of the initial model of the definition: two ground terms denote one
//! value exactly when every model of the definition equates them. Differing in *every* model is
//! not attainable for an overload application, since outside the instances of its equations a
//! model may interpret an equation head as it likes.
//!
//! The backend reads a definition by its normal-form model `M_NF` (`docs/compatibility.md`,
//! "Anywhere rules"): each sort is interpreted by the normal forms of innermost evaluation and
//! each symbol by normalizing its application. `M_NF` is a model of the definition when
//! evaluation terminates and the critical pairs of the executable equations join. The argument
//! assumes:
//!
//! - **A1 (termination).** Evaluation terminates, as every evaluation assumes.
//! - **A2 (lemmas).** The axioms no check pairs, `simplification` lemmas and `[symbolic]`
//!   function equations, are theorems of the executable equations, as every use of them assumes
//!   (compat, "Anywhere rules"), and the declarations the check reads as true hold (the verdict
//!   contract of `CheckScope::All`).
//!
//! A local check cannot replace the global one. An identification anywhere reaches other terms
//! through congruence: if two terms are equal, every equation that tells them apart equates its
//! results. Two equations `p(_:Id, _:Ids) => a` and `p(_:Exp, _:Exps) => bb`, overlapping only
//! modulo an overload axiom, equate `a` with `bb`, and a broken overload family's
//! `inj{Ids,Exps}(.Ids) = .Exps = inj{Vals,Exps}(.Vals)` reaches `a` and `bb` through
//! `pick(.Ids) => a` and `pick(.Vals) => bb`. KORE has no axiom keeping injections from different
//! source sorts apart, so such a theory stays consistent and equates terms that are syntactically
//! different and free of every symbol involved. Hence the whole definition must be shown
//! confluent.
//!
//! When the full check reports nothing, then under A1 and A2 `M_NF` is a model of the
//! definition. Every data term is a normal form: no executable equation is rooted at a free
//! constructor, an injection or a collection (no precondition row), and an instance-normal
//! overload application over normal forms is one. Distinct normal forms are distinct elements of
//! `M_NF`, so two different data terms are kept apart by a model, and they differ in the initial
//! model. (Syntactic difference is read on k-rust's internal normal form, below.)
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
//! [`BackendDefinition::is_data`] with that definition's own [`DataHeads`] (its own full check,
//! equations and overload families, its own full subsort order through its matcher), so each of
//! the two definitions must have data. Then, by the argument
//! above under A1 and A2 for each definition, two different such terms denote different values of
//! each definition's initial model, so `tm` differs from every `tb` whichever theory reads them.
//! Syntactic difference is read on k-rust's internal normal form, whose injections are taken
//! from the term's own sort (nested injections compose), which does not depend on the
//! definition. A term that does not internalize in a definition (a symbol it lacks) is not data
//! there.

use std::collections::BTreeSet;

use crate::{
    definition::BackendDefinition,
    rule::{RuleRhs, TermIndex},
    term::{HeadRole, Name, Term, TermKind},
};

/// The overload data heads of one definition and the findings of its full critical-pair check
/// (the [module documentation](self), "The class"), built by [`BackendDefinition::data_heads`]
/// and read only by [`BackendDefinition::is_data`] of the same definition.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DataHeads {
    heads: BTreeSet<Name>,
    /// Why the definition's equations are not shown confluent: one line per pair of executable
    /// equations the full check does not join, per equation the evaluator does not apply to
    /// every subject it describes, and per precondition row the definition violates. When there
    /// is one, no term is data.
    findings: Vec<String>,
}

impl DataHeads {
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

    /// Whether the full critical-pair check shows the definition's equations confluent: no
    /// finding. Otherwise no term is data.
    #[must_use]
    pub fn confluent(&self) -> bool {
        self.findings.is_empty()
    }

    /// Why the definition's equations are not shown confluent, one line each (empty when they
    /// are).
    #[must_use]
    pub fn findings(&self) -> &[String] {
        &self.findings
    }
}

impl BackendDefinition {
    /// The overload data heads of this definition and the findings of its full critical-pair
    /// check (the [module documentation](self), "The class"). The check runs in
    /// [`CheckScope::All`](crate::confluence::CheckScope::All), which classifies every pair of
    /// executable equations, not only those that can change a value claim; it costs about as
    /// much as the definition's load (0.03 s on SIMPLE, 0.2 s on WASM), so a client computes
    /// this once per definition. A head is an `anywhere` production that is not a declared
    /// function, has no hook, roots no simplification, roots at least one executable equation
    /// and only canonically shaped overload equations rooted at itself; when the check has a
    /// finding there is no head.
    #[must_use]
    pub fn data_heads(&self) -> DataHeads {
        let verdict = self.value_claims_in_scope(crate::confluence::CheckScope::All);
        let findings = confluence_findings(&verdict);
        if !findings.is_empty() {
            return DataHeads {
                heads: BTreeSet::new(),
                findings,
            };
        }
        let mut heads = BTreeSet::new();
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
            let mut rules = groups.values().flatten().peekable();
            let overload_only = rules.peek().is_some()
                && rules.all(|rule| {
                    rule.attributes.executable && canonical_overload_equation(name, rule)
                });
            if overload_only {
                heads.insert(name.clone());
            }
        }
        DataHeads { heads, findings }
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
        if !heads.confluent() {
            return false;
        }
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

/// One line per finding of a full critical-pair check: each pair it does not join (and each
/// equation the evaluator does not apply to every subject it describes), and each precondition
/// row the definition violates.
fn confluence_findings(verdict: &crate::confluence::ValueClaims) -> Vec<String> {
    let name = |rule: &crate::rule::RewriteRule| rule.attributes.diagnostic_name(str::to_owned);
    let mut findings: Vec<String> = verdict
        .violations()
        .iter()
        .map(|violation| match &violation.rule {
            Some(rule) => format!("{} ({})", violation.kind, name(rule)),
            None => violation.kind.to_string(),
        })
        .collect();
    findings.extend(verdict.unjoined().iter().map(|pair| {
        if pair.reason.describes_one_equation() {
            format!(
                "the equation {} is not applied to every subject it describes ({})",
                name(&pair.first),
                pair.reason
            )
        } else {
            format!(
                "the equations {} and {} are not shown to join ({})",
                name(&pair.first),
                name(&pair.second),
                pair.reason
            )
        }
    }));
    findings
}
