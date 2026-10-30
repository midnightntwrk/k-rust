//! Definition-derived finite scalar decisions, without executing or assuming a source row.
//!
//! A catalog borrows one actual immutable definition. It has no query facts, SMT names, widths
//! or models. Admission sees every offered function/simplification equation and requires the
//! definition's equation-selection completeness token. Only matcher refutations discard unmatched
//! source patterns. Remaining row guards must partition globally defined Boolean tests; every body/guard dependency is admitted
//! recursively on its specialized signature. Each leaf retains its canonical source domain.
//! Partial helpers use the selected domain; total declarations retain an opaque total value
//! outside the source-safe region. Neither caller bounds nor branch guards become totality. This module does not install summaries as equations or axioms.
//!
//! A function equation's row is guarded by its own match and requires, and by the inapplicability
//! of every function equation of a higher priority (`owise` included): K tries a lower priority
//! only where no higher one applies. An integer literal argument pattern is the test
//! `formal = literal`; two such tests of one formal at distinct literals exclude each other. A
//! declared-total function's value where no row applies is its own uninterpreted application
//! ([`Decision::Opaque`]); a partial function's is not given ([`Rejected::Incomplete`]).
//! A value of a sort other than `Int` or `Bool` is admitted only as a free constructor's
//! application or an injection, over admitted values: the solver reads it as an uninterpreted
//! congruent head, so two summaries agree where their decisions reach the same constructor term.
//!
//! Discovery and decision-tree construction are explicitly bounded. Every new node/candidate
//! polls the request stop; cancellation is propagated and never cached as ineligibility.
//! Boolean conjunction/disjunction guards retain both polarities as bounded DAGs. Partitioning
//! takes Shannon cofactors without eager DNF expansion; guard visits and copied child handles
//! consume the existing catalog work allowance, in addition to structural atom comparisons.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust_kore::names::BuiltinSort;
use rustc_hash::FxHashSet;

use crate::{
    builtin::{read_bool as boolean, read_int},
    definedness::ceil_term,
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::{
        Concreteness, Predicate, RewriteRule, RuleRhs, TermIndex, applicable_groups, rename_apart,
        term_index,
    },
    stop::{self, Stoppable},
    substitution::substitute,
    term::{
        DomainKind, FunctionType, HeadRole, Name, Sort, SymbolType, Term, TermKind, Variable,
        VariableKind,
    },
};

mod emission;
#[cfg(test)]
mod tests;
pub(super) use emission::{Source, prepare};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Reading {
    pub summary: Arc<Summary>,
    pub name: String,
    pub domain_name: Option<String>,
    pub exactness: super::Exactness,
}

/// Metadata lookup is not admission of the actual operands. Every consumer must retain its
/// application-use purity and definedness checks, even after a signature has been admitted.
pub(super) fn reading<'a>(
    readings: &'a BTreeMap<Key, Reading>,
    call: &Term,
) -> Option<&'a Reading> {
    if readings.is_empty() {
        return None;
    }
    let TermKind::Application {
        symbol,
        sort_arguments,
        arguments,
    } = call.kind()
    else {
        return None;
    };
    if symbol.attributes.hook.is_some()
        || symbol.attributes.smt.is_some()
        || !matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
    {
        return None;
    }
    let key = Key {
        name: symbol.name.clone(),
        sort_arguments: sort_arguments.to_vec(),
        argument_sorts: arguments.iter().map(Term::sort).collect(),
        result: call.sort(),
        static_arguments: arguments
            .iter()
            .map(|a| (!scalar(a.sort())).then(|| a.clone()))
            .collect(),
    };
    readings.get(&key)
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct Key {
    pub name: Name,
    pub sort_arguments: Vec<Sort>,
    pub argument_sorts: Vec<Sort>,
    pub result: Sort,
    pub static_arguments: Vec<Option<Term>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum Atom {
    Bool(Term),
    Less(Term, Term),
    Equal(Term, Term),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Test {
    atom: Atom,
    positive: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Decision {
    Value(Term),
    /// A declared-total function where none of its rows applies: the function's own
    /// uninterpreted application, constrained by nothing but its totality.
    Opaque,
    If {
        test: Atom,
        yes: Arc<Decision>,
        no: Arc<Decision>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct Summary {
    pub key: Key,
    pub parameters: Vec<Variable>,
    pub formal: Term,
    pub body: Arc<Decision>,
    pub domains: BTreeMap<Term, Arc<[Predicate]>>,
    pub declared_total: bool,
    pub domain_total: bool,
    pub dependencies: BTreeSet<Key>,
    /// The actual source rules, retaining every collapsed origin, not just an authored label.
    pub source_rules: Vec<Arc<RewriteRule>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Rejected {
    Unsupported,
    Incomplete,
    Overlapping,
    Restricted,
    /// The unconditional domain was not established; this is not a claim of undefinedness.
    Partial,
    Recursive,
    Limit,
}

#[derive(Clone, Copy)]
pub(super) struct Limits {
    pub specializations: usize,
    pub work: usize,
    pub depth: usize,
    pub rows: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            specializations: 128,
            work: 16_384,
            depth: 64,
            rows: 64,
        }
    }
}

pub(super) struct Catalog<'d> {
    definition: &'d BackendDefinition,
    limits: Limits,
    remaining: usize,
    effects: Option<BTreeSet<String>>,
    accepted: BTreeMap<Key, Arc<Summary>>,
    rejected: BTreeMap<Key, Rejected>,
    active: BTreeSet<Key>,
}

#[derive(Clone)]
struct Row {
    guard: Arc<Guard>,
    value: Term,
}

/// Propositional structure of globally defined source tests. Keeping a guard as a DAG
/// avoids expanding disjunctions to DNF before the bounded partition walk needs them.
#[derive(Clone)]
enum Guard {
    Constant(bool),
    Test(Test),
    And(Vec<Arc<Guard>>),
    Or(Vec<Arc<Guard>>),
}

impl Guard {
    fn junction(parts: Vec<Arc<Self>>, and: bool) -> Arc<Self> {
        let mut kept = Vec::new();
        for part in parts {
            match part.as_ref() {
                Self::Constant(value) if *value != and => return part,
                Self::Constant(_) => {}
                Self::Test(_) | Self::And(_) | Self::Or(_) => kept.push(part),
            }
        }
        match kept.len() {
            0 => Arc::new(Self::Constant(and)),
            1 => kept.pop().unwrap(),
            _ if and => Arc::new(Self::And(kept)),
            _ => Arc::new(Self::Or(kept)),
        }
    }
}

struct Specialization {
    key: Key,
    formal: Term,
    parameters: Vec<Variable>,
}

impl<'d> Catalog<'d> {
    pub fn new(definition: &'d BackendDefinition) -> Self {
        Self::with_limits(definition, Limits::default())
    }

    pub fn with_limits(definition: &'d BackendDefinition, limits: Limits) -> Self {
        Self {
            definition,
            limits,
            remaining: limits.work,
            effects: definition.console_effect_symbols(),
            accepted: BTreeMap::new(),
            rejected: BTreeMap::new(),
            active: BTreeSet::new(),
        }
    }

    fn work(&mut self) -> Stoppable<Result<(), Rejected>> {
        stop::check()?;
        if self.remaining == 0 {
            return Ok(Err(Rejected::Limit));
        }
        self.remaining -= 1;
        Ok(Ok(()))
    }

    fn signature(&mut self, call: &Term) -> Stoppable<Result<Specialization, Rejected>> {
        admitted!(self.work());
        let TermKind::Application {
            symbol,
            sort_arguments,
            arguments,
        } = call.kind()
        else {
            return Ok(Err(Rejected::Unsupported));
        };
        let eligible = matches!(
            symbol.attributes.head_role(),
            HeadRole::Function { declared: true, .. }
        ) && matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
            && symbol.attributes.hook.is_none()
            && symbol.attributes.smt.is_none()
            && !symbol.attributes.binder
            && !symbol.attributes.macro_or_alias
            && self
                .effects
                .as_ref()
                .is_some_and(|e| !e.contains(symbol.name.as_ref()))
            && (standard_scalar(self.definition, call.sort()) || data_sort(call.sort()))
            && !sort_arguments.iter().any(Sort::has_variable)
            && !arguments.iter().any(|arg| arg.sort().has_variable());
        if !eligible {
            return Ok(Err(Rejected::Unsupported));
        }
        let mut static_arguments = Vec::new();
        let mut parameters = Vec::new();
        let mut formals = Vec::new();
        if arguments.len() > self.remaining {
            return Ok(Err(Rejected::Limit));
        }
        for (index, arg) in arguments.iter().enumerate() {
            admitted!(self.work());
            if scalar(arg.sort()) {
                if !standard_scalar(self.definition, arg.sort()) {
                    return Ok(Err(Rejected::Unsupported));
                }
                let var = Variable::new(format!("KRUST-SCALAR-{index}"), arg.sort());
                formals.push(Term::variable(var.clone()));
                parameters.push(var);
                static_arguments.push(None);
            } else {
                if !arg.attributes().variables.is_empty() {
                    return Ok(Err(Rejected::Unsupported));
                }
                let mut pending = vec![arg];
                while let Some(node) = pending.pop() {
                    admitted!(self.work());
                    match node.kind() {
                        TermKind::Application {
                            symbol, arguments, ..
                        } if symbol.attributes.head_role() == HeadRole::FreeConstructor => {
                            if arguments.len() > self.remaining {
                                return Ok(Err(Rejected::Limit));
                            }
                            pending.extend(arguments.iter());
                        }
                        TermKind::DomainValue { .. } => {}
                        TermKind::Injection { term, .. } => pending.push(term),
                        TermKind::Application { .. }
                        | TermKind::Variable(_)
                        | TermKind::And(..)
                        | TermKind::Map { .. }
                        | TermKind::List { .. }
                        | TermKind::Set { .. } => return Ok(Err(Rejected::Unsupported)),
                    }
                }
                formals.push(arg.clone());
                static_arguments.push(Some(arg.clone()));
            }
        }
        let key = Key {
            name: symbol.name.clone(),
            sort_arguments: sort_arguments.to_vec(),
            argument_sorts: arguments.iter().map(Term::sort).collect(),
            result: call.sort(),
            static_arguments,
        };
        let formal = Term::application(symbol.clone(), sort_arguments.to_vec(), formals);
        Ok(Ok(Specialization {
            key,
            formal,
            parameters,
        }))
    }

    /// Derive the definition's meaning for element-valued scalar formals at this static
    /// specialization. This is not an application-use certificate: an emitter must separately
    /// check the actual operands with the existing pure-functional eligibility policy and keep
    /// their original definedness. In particular, cached metadata cannot admit set variables,
    /// binders or impure actual arguments just because their signature matches.
    pub fn admit(&mut self, call: &Term) -> Stoppable<Result<Arc<Summary>, Rejected>> {
        let Specialization {
            key,
            formal,
            parameters,
        } = admitted!(self.signature(call));
        if let Some(found) = self.accepted.get(&key) {
            return Ok(Ok(found.clone()));
        }
        if let Some(reason) = self.rejected.get(&key) {
            return Ok(Err(*reason));
        }
        if self.active.contains(&key) {
            return Ok(Err(Rejected::Recursive));
        }
        if self.accepted.len() + self.rejected.len() + self.active.len()
            >= self.limits.specializations
            || self.active.len() >= self.limits.depth
        {
            return Ok(Err(Rejected::Limit));
        }
        self.active.insert(key.clone());
        let result = self.compile(key.clone(), formal, parameters);
        self.active.remove(&key);
        match &result {
            Ok(Ok(summary)) => {
                self.accepted.insert(key, summary.clone());
            }
            Ok(Err(reason)) if *reason != Rejected::Limit => {
                self.rejected.insert(key, *reason);
            }
            // Stops and resource refusal must not become persistent ineligibility.
            Ok(Err(_)) | Err(_) => {}
        }
        result
    }

    fn compile(
        &mut self,
        key: Key,
        formal: Term,
        parameters: Vec<Variable>,
    ) -> Stoppable<Result<Arc<Summary>, Rejected>> {
        if self.definition.equation_selection_complete().is_none() {
            return Ok(Err(Rejected::Unsupported));
        }
        // Each offered rule with whether it is a function equation, whose priority ranks it in
        // the function's cascade; a simplification is an axiom of every priority alike.
        let mut offered = Vec::new();
        let index = term_index(&formal);
        for (theory, equation) in [
            (self.definition.function_theory(), true),
            (self.definition.simplification_theory(), false),
        ] {
            // Refuse a large bucket before the common selector clones its rows. Never
            // truncate that selector's result and mistake the prefix for the full definition.
            let count = [&index, &TermIndex::Variable]
                .into_iter()
                .filter_map(|i| theory.get(i))
                .flat_map(|groups| groups.values())
                .fold(0usize, |n, rows| n.saturating_add(rows.len()));
            if count > self.limits.rows.saturating_sub(offered.len()) {
                return Ok(Err(Rejected::Limit));
            }
            for group in applicable_groups(theory, &index).into_values() {
                for rule in group {
                    admitted!(self.work());
                    if offered.len() == self.limits.rows {
                        return Ok(Err(Rejected::Limit));
                    }
                    offered.push((rule, equation));
                }
            }
        }
        // A separate offered ceil theory is authoritative source meaning. This extension
        // derives a helper domain only from its complete finite value equations.
        if !applicable_groups(self.definition.ceil_theory(), &index).is_empty() {
            return Ok(Err(Rejected::Unsupported));
        }
        let declared_total = matches!(formal.kind(), TermKind::Application { symbol, .. }
            if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Total));
        let mut domains = BTreeMap::new();
        let mut rows = Vec::new();
        let mut source_rules = Vec::new();
        let mut dependencies = BTreeSet::new();
        let mut seen = FxHashSet::default();
        // The negated guards of the function equations of every priority above the current one,
        // and the current priority with its own guards: `applicable_groups` yields priorities in
        // ascending order, so a later equation ranks no higher than an earlier one.
        let mut excluded: Vec<Arc<Guard>> = Vec::new();
        let mut current: Option<(u8, Vec<Arc<Guard>>)> = None;
        for (source, equation) in offered {
            admitted!(self.work());
            let apart = rename_apart(&source, &formal.attributes().variables, &[]);
            let rule = apart.as_ref().map_or(source.as_ref(), |(rule, _)| rule);
            let (bindings, remainder) = match match_terms_in_definition(
                MatchMode::Evaluate,
                self.definition,
                &rule.lhs,
                &formal,
            ) {
                MatchResult::Failed(_) => continue,
                MatchResult::Success(bindings) => (bindings, Vec::new()),
                MatchResult::Indeterminate {
                    substitution,
                    remainder,
                } => (substitution, remainder),
                MatchResult::Undecided(_) => return Ok(Err(Rejected::Unsupported)),
            };
            if (!equation && rule.attributes.priority != 50)
                || rule.attributes.concreteness != Concreteness::Unconstrained
                || !rule.attributes.executable
                || !rule.ensures.is_empty()
                || !rule.existentials.is_empty()
                || !rule.computed_attributes.unbound_variables.is_empty()
                || rule.attributes.overload.is_some()
                || !matches!(rule.lhs.kind(), TermKind::Application { .. })
            {
                return Ok(Err(Rejected::Restricted));
            }
            let RuleRhs::Term(rhs) = &rule.rhs else {
                return Ok(Err(Rejected::Unsupported));
            };
            let value = substitute(rhs, &bindings);
            admitted!(self.check_body(&value, &parameters, &mut seen, &mut dependencies, true));
            let domain =
                admitted!(self.body_domain(&value, &parameters, &mut seen, &mut dependencies));
            domains.insert(value.clone(), domain.into());
            // Instantiate conditions through the same faithful/definedness boundary as rewrite
            // applicability. Raw conditions are never sent directly to a solver or evaluator.
            let condition = rule
                .requires
                .instantiate(&bindings)
                .with_definedness(self.definition, &[]);
            stop::check()?;
            let condition = match condition {
                Ok(predicates) => predicates,
                Err(_) => return Ok(Err(Rejected::Partial)),
            };
            // The condition is read as stated (`with_stated_ceil_conditions`): a partial hook's
            // ceil condition keeps conjuncts such as `2 =/=Int 0`, `\ceil(X)` and `\ceil(2)`.
            // A conjunct that builtin hooks alone decide true (`deferred::hooks_establish`: the
            // `\ceil` of a term without partial symbols, a ground hook condition) holds in every
            // state, so dropping it leaves a conjunction that denotes the same set, and no
            // equation is applied. Every other conjunct must pass `check_guard`.
            let mut stated = Vec::new();
            for predicate in condition {
                if !crate::deferred::hooks_establish(
                    self.definition,
                    std::slice::from_ref(&predicate),
                    &[],
                )? {
                    stated.push(predicate);
                }
            }
            let mut guards = Vec::new();
            for predicate in stated {
                let predicate = admitted!(self.check_guard(
                    &predicate,
                    &parameters,
                    &mut seen,
                    &mut dependencies,
                    0
                ));
                guards.push(admitted!(self.guard_of(&predicate, true, 0)));
            }
            for (left, right) in remainder {
                // Only Boolean and integer literal patterns become finite scalar tests. Other
                // contingent matches must not be silently promoted to an exhaustive source
                // partition.
                let (term, test, positive) = if let Some(value) = boolean(&left) {
                    (right.clone(), Predicate::Term(right), value)
                } else if let Some(value) = boolean(&right) {
                    (left.clone(), Predicate::Term(left), value)
                } else if integer_pair(&left, &right)
                    && read_int(&left).is_some() != read_int(&right).is_some()
                {
                    let term = if read_int(&left).is_some() {
                        &right
                    } else {
                        &left
                    };
                    (term.clone(), Predicate::Equals(left, right), true)
                } else {
                    return Ok(Err(Rejected::Unsupported));
                };
                admitted!(self.check_body(&term, &parameters, &mut seen, &mut dependencies, false));
                guards.push(admitted!(self.guard_of(&test, positive, 0)));
            }
            let own = Guard::junction(guards, true);
            let mut guard = own.clone();
            if equation {
                let priority = rule.attributes.priority;
                if current.as_ref().is_some_and(|(rank, _)| *rank != priority) {
                    let (_, done) = current.take().expect("a current priority");
                    for applies in done {
                        excluded.push(admitted!(self.negate(&applies)));
                    }
                }
                current
                    .get_or_insert_with(|| (priority, Vec::new()))
                    .1
                    .push(own);
                if !excluded.is_empty() {
                    guard = Guard::junction(
                        std::iter::once(guard)
                            .chain(excluded.iter().cloned())
                            .collect(),
                        true,
                    );
                }
            }
            rows.push(Row { guard, value });
            source_rules.push(source);
        }
        let domain_total = domains
            .values()
            .all(|domain: &Arc<[Predicate]>| domain.is_empty());
        let body = admitted!(self.partition(rows, declared_total, 0));
        // A function no row applies to anywhere is its own application everywhere: a summary
        // would only rename it.
        if matches!(body.as_ref(), Decision::Opaque) {
            return Ok(Err(Rejected::Incomplete));
        }
        Ok(Ok(Arc::new(Summary {
            key,
            parameters,
            formal,
            body,
            domains,
            declared_total,
            domain_total,
            dependencies,
            source_rules,
        })))
    }

    fn check_body(
        &mut self,
        root: &Term,
        parameters: &[Variable],
        seen: &mut FxHashSet<(Term, bool)>,
        dependencies: &mut BTreeSet<Key>,
        allow_partial: bool,
    ) -> Stoppable<Result<(), Rejected>> {
        let mut pending = vec![root.clone()];
        while let Some(term) = pending.pop() {
            if !seen.insert((term.clone(), allow_partial)) {
                continue;
            }
            admitted!(self.work());
            if !standard_scalar(self.definition, term.sort()) {
                // A value of another sort is a free constructor's application or an injection,
                // which the solver reads as an uninterpreted congruent head, or an unhooked
                // function's call, admitted below as a scalar one is.
                match term.kind() {
                    TermKind::Application {
                        symbol, arguments, ..
                    } if data_sort(term.sort())
                        && matches!(symbol.attributes.head_role(), HeadRole::FreeConstructor) =>
                    {
                        if arguments.len() > self.remaining {
                            return Ok(Err(Rejected::Limit));
                        }
                        pending.extend(arguments.iter().cloned());
                        continue;
                    }
                    TermKind::Injection { term: child, .. } if data_sort(term.sort()) => {
                        pending.push(child.clone());
                        continue;
                    }
                    TermKind::Application { symbol, .. }
                        if data_sort(term.sort())
                            && symbol.attributes.hook.is_none()
                            && matches!(symbol.attributes.symbol_type, SymbolType::Function(_)) => {
                    }
                    TermKind::Application { .. }
                    | TermKind::Injection { .. }
                    | TermKind::And(..)
                    | TermKind::DomainValue { .. }
                    | TermKind::Variable(_)
                    | TermKind::Map { .. }
                    | TermKind::List { .. }
                    | TermKind::Set { .. } => return Ok(Err(Rejected::Unsupported)),
                }
            }
            match term.kind() {
                TermKind::Variable(v)
                    if v.kind == VariableKind::Element && parameters.contains(v) => {}
                TermKind::DomainValue { .. } => {}
                TermKind::Application {
                    symbol, arguments, ..
                } => {
                    if arguments.len() > self.remaining {
                        return Ok(Err(Rejected::Limit));
                    }
                    if symbol.attributes.binder
                        || symbol.attributes.macro_or_alias
                        || !self
                            .effects
                            .as_ref()
                            .is_some_and(|e| !e.contains(symbol.name.as_ref()))
                    {
                        return Ok(Err(Rejected::Unsupported));
                    }
                    if symbol.attributes.hook.is_none() {
                        let summary = admitted!(self.admit(&term));
                        if !allow_partial && !summary.declared_total && !summary.domain_total {
                            return Ok(Err(Rejected::Partial));
                        }
                        dependencies.insert(summary.key.clone());
                        // Static constructor operands are already validated by signature().
                        pending.extend(arguments.iter().filter(|a| scalar(a.sort())).cloned());
                    } else {
                        if !matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
                            || !arguments.iter().all(|a| scalar(a.sort()))
                        {
                            return Ok(Err(Rejected::Unsupported));
                        }
                        // Partition tests must be globally defined. Body expressions instead
                        // retain their canonical domains in body_domain; no branch guard or
                        // call-site assumption supplies global totality here.
                        let obligations = if allow_partial {
                            Ok(Vec::new())
                        } else if symbol.attributes.symbol_type
                            == SymbolType::Function(FunctionType::Total)
                        {
                            // Strict children are checked separately below. A full ceil walk
                            // here would lose a child's source-derived globally true domain.
                            Ok(Vec::new())
                        } else {
                            crate::definedness::apply_ceil_equation(self.definition, &term)
                                .ok_or(())
                        };
                        stop::check()?;
                        let obligations = match obligations {
                            Ok(conditions) => conditions,
                            Err(_) => return Ok(Err(Rejected::Partial)),
                        };
                        // The test's global definedness is decided by builtin hooks alone, with
                        // no equation of the definition: the term is the definition's, and
                        // preparing a query must end whatever its equations do. A guard with a
                        // partial hook is admitted exactly when hooks fold every conjunct of the
                        // hook's stated ceil condition to `true`, the `\ceil` of a term without
                        // partial symbols or of a direct argument counting as holding (`compile`
                        // drops the same conjuncts from a rule's condition): `X /Int 2` and
                        // `X /Int (4 /Int 2)` are admitted (`2 =/=Int 0`). A conjunct only an
                        // equation or a simplification lemma would decide (`X /Int c()` with
                        // `c() => 2`, `X /Int (absInt(X) +Int 1)`, `X /Int (X -Int X +Int 1)`)
                        // rejects the summary, which leaves the solver less informed and never
                        // wrong. The arguments' own definedness is checked below (`allow_partial`
                        // is false for them too).
                        if !obligations.is_empty()
                            && !crate::deferred::hooks_establish(
                                self.definition,
                                &obligations,
                                arguments,
                            )?
                        {
                            return Ok(Err(Rejected::Partial));
                        }
                        pending.extend(arguments.iter().cloned());
                    }
                }
                TermKind::Variable(_)
                | TermKind::And(..)
                | TermKind::Injection { .. }
                | TermKind::Map { .. }
                | TermKind::List { .. }
                | TermKind::Set { .. } => return Ok(Err(Rejected::Unsupported)),
            }
        }
        Ok(Ok(()))
    }

    /// A leaf's source domain, independent of its partition guard and of every caller.
    /// Bound tree conversion work before invoking the canonical definedness machinery.
    fn body_domain(
        &mut self,
        body: &Term,
        parameters: &[Variable],
        seen: &mut FxHashSet<(Term, bool)>,
        dependencies: &mut BTreeSet<Key>,
    ) -> Stoppable<Result<Vec<Predicate>, Rejected>> {
        if body.attributes().ceil_free() {
            return Ok(Ok(Vec::new()));
        }
        let mut pending = vec![body];
        while let Some(term) = pending.pop() {
            admitted!(self.work());
            let children = crate::deferred::children(term);
            if children.len() > self.remaining {
                return Ok(Err(Rejected::Limit));
            }
            pending.extend(children);
        }
        let obligations = match ceil_term(self.definition, body) {
            Ok(obligations) => obligations,
            Err(_) => return Ok(Err(Rejected::Partial)),
        };
        stop::check()?;
        let obligations =
            match crate::definedness::request_definedness(self.definition, obligations) {
                Ok(obligations) => obligations,
                Err(_) => return Ok(Err(Rejected::Partial)),
            };
        let mut pending = obligations.iter().collect::<Vec<_>>();
        while let Some(predicate) = pending.pop() {
            admitted!(self.work());
            match predicate {
                Predicate::True | Predicate::False => {}
                Predicate::Term(t) => {
                    admitted!(self.check_body(t, parameters, seen, dependencies, true));
                }
                Predicate::Equals(a, b) => {
                    admitted!(self.check_body(a, parameters, seen, dependencies, true));
                    admitted!(self.check_body(b, parameters, seen, dependencies, true));
                }
                Predicate::Ceil(call) | Predicate::Defined(call) => {
                    // A dependency's complete decision graph supplies its domain. An
                    // unresolved primitive domain is not evidence of bottom or totality.
                    if matches!(call.kind(), TermKind::Application { symbol, .. } if symbol.attributes.hook.is_some())
                    {
                        if crate::definedness::apply_ceil_equation(self.definition, call).is_some()
                        {
                            // Pure deferred operands retain their canonical primitive domain;
                            // the query's domain planner prepares it without evaluation.
                            continue;
                        }
                        return Ok(Err(Rejected::Partial));
                    }
                    let summary = admitted!(self.admit(call));
                    dependencies.insert(summary.key.clone());
                }
                Predicate::Not(p) => pending.push(p),
                Predicate::And(ps) | Predicate::Or(ps) => pending.extend(ps.iter()),
                Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                    pending.extend([a.as_ref(), b.as_ref()])
                }
                Predicate::Floor(_)
                | Predicate::In(..)
                | Predicate::Exists(..)
                | Predicate::Forall(..)
                | Predicate::Absent(_) => return Ok(Err(Rejected::Unsupported)),
            }
        }
        Ok(Ok(obligations
            .into_iter()
            .filter(|p| *p != Predicate::True)
            .collect()))
    }

    fn check_guard(
        &mut self,
        predicate: &Predicate,
        parameters: &[Variable],
        seen: &mut FxHashSet<(Term, bool)>,
        dependencies: &mut BTreeSet<Key>,
        depth: usize,
    ) -> Stoppable<Result<Predicate, Rejected>> {
        admitted!(self.work());
        if depth >= self.limits.depth {
            return Ok(Err(Rejected::Limit));
        }
        let checked = match predicate {
            Predicate::True | Predicate::False => predicate.clone(),
            Predicate::Term(t) => {
                admitted!(self.check_body(t, parameters, seen, dependencies, false));
                predicate.clone()
            }
            Predicate::Equals(a, b) => {
                admitted!(self.check_body(a, parameters, seen, dependencies, false));
                admitted!(self.check_body(b, parameters, seen, dependencies, false));
                predicate.clone()
            }
            Predicate::Not(p) => Predicate::Not(Arc::new(admitted!(self.check_guard(
                p,
                parameters,
                seen,
                dependencies,
                depth + 1
            )))),
            Predicate::And(parts) | Predicate::Or(parts) => {
                if parts.len() > self.remaining {
                    return Ok(Err(Rejected::Limit));
                }
                let mut checked = Vec::new();
                for part in parts.iter() {
                    checked.push(admitted!(self.check_guard(
                        part,
                        parameters,
                        seen,
                        dependencies,
                        depth + 1
                    )));
                }
                if matches!(predicate, Predicate::And(_)) {
                    Predicate::And(checked.into())
                } else {
                    Predicate::Or(checked.into())
                }
            }
            Predicate::Ceil(call) | Predicate::Defined(call) => {
                // A nominally partial helper may have a complete, globally defined source
                // graph. This permits that graph as a partition test, not a partial guard.
                // Checking the whole call also retains global definedness of every argument.
                admitted!(self.check_body(call, parameters, seen, dependencies, false));
                let summary = admitted!(self.admit(call));
                if !summary.declared_total && !summary.domain_total {
                    return Ok(Err(Rejected::Partial));
                }
                dependencies.insert(summary.key.clone());
                Predicate::True
            }
            Predicate::Floor(_)
            | Predicate::In(..)
            | Predicate::Implies(..)
            | Predicate::Iff(..)
            | Predicate::Exists(..)
            | Predicate::Forall(..)
            | Predicate::Absent(_) => return Ok(Err(Rejected::Unsupported)),
        };
        Ok(Ok(crate::simplify::normalize_predicate(checked)))
    }

    /// ```toml algorithm-site
    /// id = "backend.smt.check"
    /// role = "part"
    /// sites = ["Catalog::partition", "Catalog::split_rows", "Catalog::cofactor", "Catalog::negate", "guard_of", "term_guard", "Guard::junction"]
    /// ```
    fn partition(
        &mut self,
        mut rows: Vec<Row>,
        total: bool,
        depth: usize,
    ) -> Stoppable<Result<Arc<Decision>, Rejected>> {
        admitted!(self.work());
        if depth >= self.limits.depth {
            return Ok(Err(Rejected::Limit));
        }
        rows.retain(|row| !matches!(row.guard.as_ref(), Guard::Constant(false)));
        if rows.is_empty() {
            // No row applies: a declared-total function still has a value there, which no
            // equation constrains; a partial one has none the source gives.
            return Ok(if total {
                Ok(Arc::new(Decision::Opaque))
            } else {
                Err(Rejected::Incomplete)
            });
        }
        if rows.len() == 1 && matches!(rows[0].guard.as_ref(), Guard::Constant(true)) {
            return Ok(Ok(Arc::new(Decision::Value(rows[0].value.clone()))));
        }
        if rows
            .iter()
            .filter(|row| matches!(row.guard.as_ref(), Guard::Constant(true)))
            .count()
            > 1
        {
            return Ok(Err(Rejected::Overlapping));
        }
        // A nonconstant guard may still be contradictory. An unconditional row overlaps
        // it only if some cofactor reaches a second true row; do not assume satisfiability.
        let mut first = rows
            .iter()
            .find(|row| !matches!(row.guard.as_ref(), Guard::Constant(true)))
            .expect("a sole unconditional row was handled above")
            .guard
            .as_ref();
        let atom = loop {
            admitted!(self.work());
            match first {
                Guard::Test(test) => break test.atom.clone(),
                Guard::And(parts) | Guard::Or(parts) => first = parts[0].as_ref(),
                Guard::Constant(_) => unreachable!("constant rows handled above"),
            }
        };
        let yes_rows = admitted!(self.split_rows(&rows, &atom, true));
        let no_rows = admitted!(self.split_rows(&rows, &atom, false));
        let yes = admitted!(self.partition(yes_rows, total, depth + 1));
        let no = admitted!(self.partition(no_rows, total, depth + 1));
        Ok(Ok(Arc::new(Decision::If {
            test: atom,
            yes,
            no,
        })))
    }

    fn split_rows(
        &mut self,
        rows: &[Row],
        atom: &Atom,
        positive: bool,
    ) -> Stoppable<Result<Vec<Row>, Rejected>> {
        let mut result = Vec::new();
        for row in rows {
            admitted!(self.work());
            let guard = admitted!(self.cofactor(&row.guard, atom, positive));
            if !matches!(guard.as_ref(), Guard::Constant(false)) {
                result.push(Row {
                    guard,
                    value: row.value.clone(),
                });
            }
        }
        Ok(Ok(result))
    }

    fn guard_of(
        &mut self,
        predicate: &Predicate,
        positive: bool,
        depth: usize,
    ) -> Stoppable<Result<Arc<Guard>, Rejected>> {
        guard_of(
            predicate,
            positive,
            &mut self.remaining,
            depth,
            self.limits.depth,
        )
    }

    /// One Shannon cofactor. Every visited guard node and copied child handle pays the
    /// definition-local work allowance; exhausted walks decline the entire summary.
    fn cofactor(
        &mut self,
        guard: &Arc<Guard>,
        atom: &Atom,
        positive: bool,
    ) -> Stoppable<Result<Arc<Guard>, Rejected>> {
        admitted!(self.work());
        match guard.as_ref() {
            Guard::Constant(_) => Ok(Ok(guard.clone())),
            Guard::Test(test) if &test.atom == atom => {
                Ok(Ok(Arc::new(Guard::Constant(test.positive == positive))))
            }
            // Where `T = c` holds, `T = d` fails for every other integer literal `d`.
            Guard::Test(test) if positive && excludes(atom, &test.atom) => {
                Ok(Ok(Arc::new(Guard::Constant(!test.positive))))
            }
            Guard::Test(_) => Ok(Ok(guard.clone())),
            Guard::And(parts) | Guard::Or(parts) => {
                if parts.len() > self.remaining {
                    return Ok(Err(Rejected::Limit));
                }
                let mut reduced = Vec::with_capacity(parts.len());
                for part in parts {
                    reduced.push(admitted!(self.cofactor(part, atom, positive)));
                }
                Ok(Ok(Guard::junction(
                    reduced,
                    matches!(guard.as_ref(), Guard::And(_)),
                )))
            }
        }
    }

    /// The complement of a guard, by De Morgan's laws down to its tests. Every guard's tests
    /// are globally defined, so the complement holds exactly where the guard fails.
    fn negate(&mut self, guard: &Arc<Guard>) -> Stoppable<Result<Arc<Guard>, Rejected>> {
        admitted!(self.work());
        match guard.as_ref() {
            Guard::Constant(value) => Ok(Ok(Arc::new(Guard::Constant(!value)))),
            Guard::Test(test) => Ok(Ok(Arc::new(Guard::Test(Test {
                atom: test.atom.clone(),
                positive: !test.positive,
            })))),
            Guard::And(parts) | Guard::Or(parts) => {
                if parts.len() > self.remaining {
                    return Ok(Err(Rejected::Limit));
                }
                let mut negated = Vec::with_capacity(parts.len());
                for part in parts {
                    negated.push(admitted!(self.negate(part)));
                }
                Ok(Ok(Guard::junction(
                    negated,
                    matches!(guard.as_ref(), Guard::Or(_)),
                )))
            }
        }
    }
}

/// Whether `known` and `other` equate one term with two distinct integer literals, so that
/// `other` fails wherever `known` holds.
fn excludes(known: &Atom, other: &Atom) -> bool {
    match (literal_equality(known), literal_equality(other)) {
        (Some((term, value)), Some((other_term, other_value))) => {
            term == other_term && value != other_value
        }
        _ => false,
    }
}

/// The term and the integer literal of an equality test `T = c`.
fn literal_equality(atom: &Atom) -> Option<(&Term, num_bigint::BigInt)> {
    let Atom::Equal(a, b) = atom else {
        return None;
    };
    match (read_int(a), read_int(b)) {
        (None, Some(value)) => Some((a, value)),
        (Some(value), None) => Some((b, value)),
        _ => None,
    }
}

/// A sort whose values a summary may build from free constructors: not `Int` or `Bool`, and
/// without sort variables.
fn data_sort(sort: Sort) -> bool {
    !scalar(sort) && !sort.has_variable()
}

fn scalar(sort: Sort) -> bool {
    sort.is_builtin(BuiltinSort::Int) || sort.is_builtin(BuiltinSort::Bool)
}

fn standard_scalar(definition: &BackendDefinition, sort: Sort) -> bool {
    (sort.is_builtin(BuiltinSort::Int) && definition.domain_kind(&sort) == Some(DomainKind::Int))
        || (sort.is_builtin(BuiltinSort::Bool)
            && definition.domain_kind(&sort) == Some(DomainKind::Bool))
}

/// Read only Boolean structure whose operands the catalog has already established globally
/// defined and pure. Other total Boolean values remain atoms; no caller facts enter a guard.
fn guard_of(
    predicate: &Predicate,
    positive: bool,
    remaining: &mut usize,
    depth: usize,
    limit: usize,
) -> Stoppable<Result<Arc<Guard>, Rejected>> {
    stop::check()?;
    if depth >= limit || *remaining == 0 {
        return Ok(Err(Rejected::Limit));
    }
    *remaining -= 1;
    let atom = match predicate {
        Predicate::True => return Ok(Ok(Arc::new(Guard::Constant(positive)))),
        Predicate::False => return Ok(Ok(Arc::new(Guard::Constant(!positive)))),
        Predicate::Not(p) => return guard_of(p, !positive, remaining, depth + 1, limit),
        Predicate::And(parts) | Predicate::Or(parts) => {
            if parts.len() > *remaining {
                return Ok(Err(Rejected::Limit));
            }
            let mut guards = Vec::with_capacity(parts.len());
            for part in parts.iter() {
                guards.push(admitted!(guard_of(
                    part,
                    positive,
                    remaining,
                    depth + 1,
                    limit
                )));
            }
            return Ok(Ok(Guard::junction(
                guards,
                matches!(predicate, Predicate::And(_)) == positive,
            )));
        }
        Predicate::Equals(left, right) if boolean(right).is_some() => {
            return term_guard(
                left,
                positive == boolean(right).unwrap(),
                remaining,
                depth + 1,
                limit,
            );
        }
        Predicate::Equals(left, right) if boolean(left).is_some() => {
            return term_guard(
                right,
                positive == boolean(left).unwrap(),
                remaining,
                depth + 1,
                limit,
            );
        }
        Predicate::Equals(a, b) if a.sort() == b.sort() && scalar(a.sort()) => {
            if a <= b {
                Atom::Equal(a.clone(), b.clone())
            } else {
                Atom::Equal(b.clone(), a.clone())
            }
        }
        Predicate::Term(term) => return term_guard(term, positive, remaining, depth + 1, limit),
        Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Implies(..)
        | Predicate::Iff(..)
        | Predicate::Exists(..)
        | Predicate::Forall(..)
        | Predicate::Absent(_)
        | Predicate::Defined(_) => return Ok(Err(Rejected::Unsupported)),
    };
    Ok(Ok(Arc::new(Guard::Test(Test { atom, positive }))))
}

fn term_guard(
    term: &Term,
    mut positive: bool,
    remaining: &mut usize,
    depth: usize,
    limit: usize,
) -> Stoppable<Result<Arc<Guard>, Rejected>> {
    stop::check()?;
    if depth >= limit || *remaining == 0 {
        return Ok(Err(Rejected::Limit));
    }
    *remaining -= 1;
    if let Some(value) = boolean(term) {
        return Ok(Ok(Arc::new(Guard::Constant(value == positive))));
    }
    if !term.sort().is_builtin(BuiltinSort::Bool) {
        return Ok(Err(Rejected::Unsupported));
    }
    let atom = if let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    {
        match (symbol.attributes.hook.as_deref(), arguments.as_slice()) {
            (Some("BOOL.not"), [inner]) if inner.sort().is_builtin(BuiltinSort::Bool) => {
                return term_guard(inner, !positive, remaining, depth + 1, limit);
            }
            (
                Some(hook @ ("BOOL.and" | "BOOL.andThen" | "BOOL.or" | "BOOL.orElse")),
                [left, right],
            ) if left.sort().is_builtin(BuiltinSort::Bool)
                && right.sort().is_builtin(BuiltinSort::Bool) =>
            {
                let a = admitted!(term_guard(left, positive, remaining, depth + 1, limit));
                let b = admitted!(term_guard(right, positive, remaining, depth + 1, limit));
                return Ok(Ok(Guard::junction(
                    vec![a, b],
                    matches!(hook, "BOOL.and" | "BOOL.andThen") == positive,
                )));
            }
            (Some("INT.lt"), [a, b]) if integer_pair(a, b) => Atom::Less(a.clone(), b.clone()),
            (Some("INT.ge"), [a, b]) if integer_pair(a, b) => {
                positive = !positive;
                Atom::Less(a.clone(), b.clone())
            }
            (Some("INT.gt"), [a, b]) if integer_pair(a, b) => Atom::Less(b.clone(), a.clone()),
            (Some("INT.le"), [a, b]) if integer_pair(a, b) => {
                positive = !positive;
                Atom::Less(b.clone(), a.clone())
            }
            (Some("INT.eq" | "INT.ne"), [a, b]) if integer_pair(a, b) => {
                if symbol.attributes.hook.as_deref() == Some("INT.ne") {
                    positive = !positive;
                }
                if a <= b {
                    Atom::Equal(a.clone(), b.clone())
                } else {
                    Atom::Equal(b.clone(), a.clone())
                }
            }
            _ => Atom::Bool(term.clone()),
        }
    } else {
        Atom::Bool(term.clone())
    };
    Ok(Ok(Arc::new(Guard::Test(Test { atom, positive }))))
}

fn integer_pair(a: &Term, b: &Term) -> bool {
    a.sort().is_builtin(BuiltinSort::Int) && b.sort().is_builtin(BuiltinSort::Int)
}

/// Propagate operation stops before considering the conservative admission failure.
macro_rules! admitted {
    ($result:expr) => {
        match $result? {
            Ok(value) => value,
            Err(reason) => return Ok(Err(reason)),
        }
    };
}
use admitted;
