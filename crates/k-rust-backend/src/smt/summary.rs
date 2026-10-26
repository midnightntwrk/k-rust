//! Definition-derived finite scalar decisions, without executing or assuming a source row.
//!
//! A catalog borrows one actual immutable definition. It has no query facts, SMT names, widths
//! or models. Admission sees every offered function/simplification equation and requires the
//! definition's equation-selection completeness token. Only matcher refutations discard rows.
//! Remaining rows must partition total Boolean tests; every body/guard dependency is admitted
//! recursively on its specialized signature. A total declaration cannot supply missing rows or
//! make a partial branch safe. This module does not install summaries as equations or axioms.
//!
//! Discovery and decision-tree construction are explicitly bounded. Every new node/candidate
//! polls the request stop; cancellation is propagated and never cached as ineligibility.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust_kore::names::BuiltinSort;
use rustc_hash::FxHashSet;

use crate::{
    builtin::read_bool as boolean,
    definedness::ceil_term,
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::{
        Concreteness, Predicate, RewriteRule, RuleRhs, TermIndex, applicable_groups, rename_apart,
        term_index,
    },
    simplify::{SimplificationError, SimplificationOptions, simplify_predicates_with_solver},
    smt::NoSolver,
    stop::{self, Stoppable},
    substitution::substitute,
    term::{
        DomainKind, FunctionType, HeadRole, Name, Sort, SymbolType, Term, TermKind, Variable,
        VariableKind,
    },
};

#[cfg(test)]
mod tests;

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
    pub body: Arc<Decision>,
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
    tests: BTreeSet<Test>,
    value: Term,
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
        ) && symbol.attributes.symbol_type
            == SymbolType::Function(FunctionType::Total)
            && symbol.attributes.hook.is_none()
            && symbol.attributes.smt.is_none()
            && !symbol.attributes.binder
            && !symbol.attributes.macro_or_alias
            && self
                .effects
                .as_ref()
                .is_some_and(|e| !e.contains(symbol.name.as_ref()))
            && standard_scalar(self.definition, call.sort())
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
        let mut offered = Vec::new();
        let index = term_index(&formal);
        for theory in [
            self.definition.function_theory(),
            self.definition.simplification_theory(),
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
                    offered.push(rule);
                }
            }
        }
        let mut rows = Vec::new();
        let mut source_rules = Vec::new();
        let mut dependencies = BTreeSet::new();
        let mut seen = FxHashSet::default();
        for source in offered {
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
            if rule.attributes.priority != 50
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
            admitted!(self.check_body(&value, &parameters, &mut seen, &mut dependencies));
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
            let mut tests = BTreeSet::new();
            for predicate in condition {
                admitted!(self.check_guard(&predicate, &parameters, &mut seen, &mut dependencies));
                admitted!(tests_of(&predicate, true, &mut tests));
            }
            for (left, right) in remainder {
                // Only Boolean literal patterns become finite scalar tests. Other contingent
                // matches must not be silently promoted to an exhaustive source partition.
                let (term, value) = if let Some(value) = boolean(&left) {
                    (right, value)
                } else if let Some(value) = boolean(&right) {
                    (left, value)
                } else {
                    return Ok(Err(Rejected::Unsupported));
                };
                admitted!(self.check_body(&term, &parameters, &mut seen, &mut dependencies));
                admitted!(tests_of(&Predicate::Term(term), value, &mut tests));
            }
            rows.push(Row { tests, value });
            source_rules.push(source);
        }
        let body = admitted!(self.partition(rows, 0));
        Ok(Ok(Arc::new(Summary {
            key,
            parameters,
            body,
            dependencies,
            source_rules,
        })))
    }

    fn check_body(
        &mut self,
        root: &Term,
        parameters: &[Variable],
        seen: &mut FxHashSet<Term>,
        dependencies: &mut BTreeSet<Key>,
    ) -> Stoppable<Result<(), Rejected>> {
        let mut pending = vec![root.clone()];
        while let Some(term) = pending.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            admitted!(self.work());
            if !standard_scalar(self.definition, term.sort()) {
                return Ok(Err(Rejected::Unsupported));
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
                        dependencies.insert(summary.key.clone());
                        // Static constructor operands are already validated by signature().
                        pending.extend(arguments.iter().filter(|a| scalar(a.sort())).cloned());
                    } else {
                        if !matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
                            || !arguments.iter().all(|a| scalar(a.sort()))
                        {
                            return Ok(Err(Rejected::Unsupported));
                        }
                        // Canonical ceil rules, not a second private domain table, establish
                        // total bodies. No branch guard or call-site assumption is supplied.
                        let obligations = ceil_term(self.definition, &term);
                        stop::check()?;
                        let obligations = match obligations {
                            Ok(conditions) => conditions,
                            Err(_) => return Ok(Err(Rejected::Partial)),
                        };
                        if !obligations.is_empty() {
                            match simplify_predicates_with_solver(
                                self.definition,
                                &obligations,
                                &[],
                                SimplificationOptions {
                                    max_iterations: 64,
                                    ..SimplificationOptions::default()
                                },
                                &NoSolver,
                            )? {
                                Ok(predicates)
                                    if predicates.is_empty()
                                        || predicates.iter().all(|p| *p == Predicate::True) => {}
                                Ok(_) => return Ok(Err(Rejected::Partial)),
                                Err(error) => {
                                    return Ok(Err(
                                        if matches!(
                                            error,
                                            SimplificationError::IterationLimit { .. }
                                                | SimplificationError::PredicateIterationLimit { .. }
                                        ) {
                                            Rejected::Limit
                                        } else {
                                            Rejected::Unsupported
                                        },
                                    ));
                                }
                            }
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

    fn check_guard(
        &mut self,
        root: &Predicate,
        parameters: &[Variable],
        seen: &mut FxHashSet<Term>,
        dependencies: &mut BTreeSet<Key>,
    ) -> Stoppable<Result<(), Rejected>> {
        let mut pending = vec![(root, 0)];
        while let Some((predicate, depth)) = pending.pop() {
            admitted!(self.work());
            if depth >= self.limits.depth {
                return Ok(Err(Rejected::Limit));
            }
            match predicate {
                Predicate::True | Predicate::False => {}
                Predicate::Term(t) => {
                    admitted!(self.check_body(t, parameters, seen, dependencies));
                }
                Predicate::Equals(a, b) => {
                    admitted!(self.check_body(a, parameters, seen, dependencies));
                    admitted!(self.check_body(b, parameters, seen, dependencies));
                }
                Predicate::Not(p) => pending.push((p, depth + 1)),
                Predicate::And(parts) => {
                    if parts.len() > self.remaining {
                        return Ok(Err(Rejected::Limit));
                    }
                    pending.extend(parts.iter().map(|p| (p, depth + 1)));
                }
                Predicate::Ceil(_)
                | Predicate::Floor(_)
                | Predicate::In(..)
                | Predicate::Or(_)
                | Predicate::Implies(..)
                | Predicate::Iff(..)
                | Predicate::Exists(..)
                | Predicate::Forall(..)
                | Predicate::Absent(_)
                | Predicate::Defined(_) => return Ok(Err(Rejected::Unsupported)),
            }
        }
        Ok(Ok(()))
    }

    fn partition(
        &mut self,
        rows: Vec<Row>,
        depth: usize,
    ) -> Stoppable<Result<Arc<Decision>, Rejected>> {
        admitted!(self.work());
        if depth >= self.limits.depth {
            return Ok(Err(Rejected::Limit));
        }
        if rows.is_empty() {
            return Ok(Err(Rejected::Incomplete));
        }
        if rows.len() == 1 && rows[0].tests.is_empty() {
            return Ok(Ok(Arc::new(Decision::Value(rows[0].value.clone()))));
        }
        if rows.iter().any(|row| row.tests.is_empty()) {
            return Ok(Err(Rejected::Overlapping));
        }
        let atom = rows[0].tests.first().expect("nonempty tests").atom.clone();
        let yes_rows = admitted!(self.split_rows(&rows, &atom, true));
        let no_rows = admitted!(self.split_rows(&rows, &atom, false));
        let yes = admitted!(self.partition(yes_rows, depth + 1));
        let no = admitted!(self.partition(no_rows, depth + 1));
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
            if row.tests.contains(&Test {
                atom: atom.clone(),
                positive: !positive,
            }) {
                continue;
            }
            // Shannon expansion can copy rows that do not mention the chosen atom. Charge
            // copied test entries before allocation, not merely the number of decision nodes.
            if row.tests.len() > self.remaining {
                return Ok(Err(Rejected::Limit));
            }
            self.remaining -= row.tests.len();
            let mut row = row.clone();
            row.tests.remove(&Test {
                atom: atom.clone(),
                positive,
            });
            result.push(row);
        }
        Ok(Ok(result))
    }
}

fn scalar(sort: Sort) -> bool {
    sort.is_builtin(BuiltinSort::Int) || sort.is_builtin(BuiltinSort::Bool)
}

fn standard_scalar(definition: &BackendDefinition, sort: Sort) -> bool {
    (sort.is_builtin(BuiltinSort::Int) && definition.domain_kind(&sort) == Some(DomainKind::Int))
        || (sort.is_builtin(BuiltinSort::Bool)
            && definition.domain_kind(&sort) == Some(DomainKind::Bool))
}

fn tests_of(
    predicate: &Predicate,
    positive: bool,
    tests: &mut BTreeSet<Test>,
) -> Stoppable<Result<(), Rejected>> {
    stop::check()?;
    match predicate {
        Predicate::True if positive => {}
        Predicate::False if !positive => {}
        Predicate::Not(p) => return tests_of(p, !positive, tests),
        Predicate::And(parts) if positive => {
            for part in parts.iter() {
                admitted!(tests_of(part, true, tests));
            }
        }
        Predicate::Equals(left, right) if boolean(right).is_some() => {
            return term_test(left, positive == boolean(right).unwrap(), tests);
        }
        Predicate::Equals(left, right) if boolean(left).is_some() => {
            return term_test(right, positive == boolean(left).unwrap(), tests);
        }
        Predicate::Equals(a, b) if a.sort() == b.sort() && scalar(a.sort()) => {
            let atom = if a <= b {
                Atom::Equal(a.clone(), b.clone())
            } else {
                Atom::Equal(b.clone(), a.clone())
            };
            return insert(tests, atom, positive);
        }
        Predicate::Term(term) => return term_test(term, positive, tests),
        Predicate::True
        | Predicate::False
        | Predicate::And(_)
        | Predicate::Equals(..)
        | Predicate::Ceil(_)
        | Predicate::Floor(_)
        | Predicate::In(..)
        | Predicate::Or(_)
        | Predicate::Implies(..)
        | Predicate::Iff(..)
        | Predicate::Exists(..)
        | Predicate::Forall(..)
        | Predicate::Absent(_)
        | Predicate::Defined(_) => return Ok(Err(Rejected::Unsupported)),
    }
    Ok(Ok(()))
}

fn term_test(
    mut term: &Term,
    mut positive: bool,
    tests: &mut BTreeSet<Test>,
) -> Stoppable<Result<(), Rejected>> {
    loop {
        stop::check()?;
        if let TermKind::Application {
            symbol, arguments, ..
        } = term.kind()
            && symbol.attributes.hook.as_deref() == Some("BOOL.not")
            && let [inner] = arguments.as_slice()
            && inner.sort().is_builtin(BuiltinSort::Bool)
        {
            term = inner;
            positive = !positive;
        } else {
            break;
        }
    }
    if let Some(value) = boolean(term) {
        return Ok(if value == positive {
            Ok(())
        } else {
            Err(Rejected::Unsupported)
        });
    }
    if !term.sort().is_builtin(BuiltinSort::Bool) {
        return Ok(Err(Rejected::Unsupported));
    }
    let atom = if let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    {
        match (symbol.attributes.hook.as_deref(), arguments.as_slice()) {
            (Some("INT.lt"), [a, b]) if integer_pair(a, b) => Atom::Less(a.clone(), b.clone()),
            (Some("INT.ge"), [a, b]) if integer_pair(a, b) => {
                return insert(tests, Atom::Less(a.clone(), b.clone()), !positive);
            }
            (Some("INT.gt"), [a, b]) if integer_pair(a, b) => Atom::Less(b.clone(), a.clone()),
            (Some("INT.le"), [a, b]) if integer_pair(a, b) => {
                return insert(tests, Atom::Less(b.clone(), a.clone()), !positive);
            }
            (Some("INT.eq" | "INT.ne"), [a, b]) if integer_pair(a, b) => {
                let atom = if a <= b {
                    Atom::Equal(a.clone(), b.clone())
                } else {
                    Atom::Equal(b.clone(), a.clone())
                };
                return insert(
                    tests,
                    atom,
                    if symbol.attributes.hook.as_deref() == Some("INT.ne") {
                        !positive
                    } else {
                        positive
                    },
                );
            }
            _ => Atom::Bool(term.clone()),
        }
    } else {
        Atom::Bool(term.clone())
    };
    insert(tests, atom, positive)
}

fn insert(
    tests: &mut BTreeSet<Test>,
    atom: Atom,
    positive: bool,
) -> Stoppable<Result<(), Rejected>> {
    tests.insert(Test { atom, positive });
    Ok(Ok(()))
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
