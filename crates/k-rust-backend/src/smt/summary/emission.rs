//! Definition-owned source and query-local shared scalar functions.
//!
//! Source identity is ownership identity, not a cross-definition cache key. The snapshot is
//! immutable; each query's admission borrows it and produces metadata containing no caller
//! bounds, SMT names or model evidence. Definitions are emitted in dependency order, and their
//! formal variables remain local SMT parameters even when actual calls occur under binders.

use std::{fmt, sync::Arc};

use rustc_hash::{FxHashMap, FxHashSet};

use super::{Atom, Catalog, Decision, Reading, Summary};
use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    smt::{
        Exactness, SExpr, SharedTerms, TranslationError, TranslationState, prelude_smt_sort, word,
    },
    stop::{self, Stoppable},
    substitution::Substitution,
    term::{SymbolType, Term, TermKind},
};

const WORK: usize = 16_384;
const TEXT: usize = 1_048_576;

#[derive(Clone)]
pub(in crate::smt) struct Source(Arc<BackendDefinition>);

impl Source {
    pub fn new(definition: &BackendDefinition) -> Self {
        Self(Arc::new(definition.clone()))
    }

    #[cfg(feature = "z3")]
    pub(in crate::smt) fn definition(&self) -> &BackendDefinition {
        &self.0
    }
}

impl fmt::Debug for Source {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ScalarSource")
            .field(&self.0.main_module())
            .finish_non_exhaustive()
    }
}

impl PartialEq for Source {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for Source {}

enum Pending<'a> {
    Predicate(&'a Predicate),
    Term(&'a Term),
}

fn calls<'a>(
    known: &'a [Predicate],
    substitution: &'a Substitution,
    checked: &'a [Predicate],
) -> Stoppable<Option<Vec<&'a Term>>> {
    let mut remaining = WORK;
    if known
        .len()
        .saturating_add(checked.len())
        .saturating_add(substitution.len())
        > remaining
    {
        return Ok(None);
    }
    let mut pending = known
        .iter()
        .chain(checked)
        .map(Pending::Predicate)
        .chain(substitution.values().map(Pending::Term))
        .collect::<Vec<_>>();
    let mut seen = FxHashSet::default();
    let mut candidates = Vec::new();
    while let Some(node) = pending.pop() {
        stop::check()?;
        if remaining == 0 {
            return Ok(None);
        }
        remaining -= 1;
        match node {
            Pending::Predicate(predicate) => match predicate {
                Predicate::Term(term) | Predicate::Ceil(term) | Predicate::Defined(term) => {
                    pending.push(Pending::Term(term))
                }
                Predicate::Equals(a, b) => pending.extend([Pending::Term(a), Pending::Term(b)]),
                Predicate::Not(p) | Predicate::Forall(_, p) | Predicate::Exists(_, p) => {
                    pending.push(Pending::Predicate(p))
                }
                Predicate::And(parts) | Predicate::Or(parts) => {
                    if parts.len() > remaining.saturating_sub(pending.len()) {
                        return Ok(None);
                    }
                    pending.extend(parts.iter().map(Pending::Predicate));
                }
                Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                    pending.extend([Pending::Predicate(a), Pending::Predicate(b)])
                }
                // These atoms do not translate their operand values.
                Predicate::True
                | Predicate::False
                | Predicate::Floor(_)
                | Predicate::In(..)
                | Predicate::Absent(_) => {}
            },
            Pending::Term(term) => {
                if !seen.insert(term) {
                    continue;
                }
                match term.kind() {
                    TermKind::Application {
                        symbol, arguments, ..
                    } => {
                        if arguments.len() > remaining.saturating_sub(pending.len()) {
                            return Ok(None);
                        }
                        if symbol.attributes.hook.is_none()
                            && symbol.attributes.smt.is_none()
                            && matches!(symbol.attributes.symbol_type, SymbolType::Function(_))
                        {
                            candidates.push(term);
                        }
                        pending.extend(arguments.iter().map(Pending::Term));
                    }
                    TermKind::Injection { term, .. } => pending.push(Pending::Term(term)),
                    TermKind::And(..)
                    | TermKind::DomainValue { .. }
                    | TermKind::Variable(_)
                    | TermKind::Map { .. }
                    | TermKind::List { .. }
                    | TermKind::Set { .. } => {}
                }
            }
        }
    }
    Ok(Some(candidates))
}

struct Body<'a> {
    state: &'a mut TranslationState,
    decisions: FxHashMap<*const Decision, (SExpr, SExpr)>,
    domains: &'a std::collections::BTreeMap<Term, Arc<[Predicate]>>,
    formal: &'a Term,
    bindings: Vec<(String, SExpr)>,
    remaining: &'a mut usize,
}

impl Body<'_> {
    fn decision(
        &mut self,
        body: &Arc<Decision>,
        depth: usize,
    ) -> Stoppable<Result<Option<(SExpr, SExpr)>, TranslationError>> {
        stop::check()?;
        if depth >= 128 || *self.remaining == 0 {
            return Ok(Ok(None));
        }
        *self.remaining -= 1;
        if let Some(value) = self.decisions.get(&Arc::as_ptr(body)) {
            return Ok(Ok(Some(value.clone())));
        }
        let value = match body.as_ref() {
            Decision::Value(term) => (|| {
                let value = self.state.translate_term(term)?;
                let domain = if self.domains[term].is_empty() {
                    SExpr::atom("true")
                } else {
                    self.state
                        .translate_predicate(&Predicate::And(self.domains[term].clone()))?
                };
                Ok((value, domain))
            })(),
            // The summary is not installed yet, so this is the ordinary pure total UF of the
            // call at its formal parameters, as the declared-total fallback below.
            Decision::Opaque => self
                .state
                .translate_term(self.formal)
                .map(|value| (value, SExpr::atom("true"))),
            Decision::If { test, yes, no } => {
                let test = match test {
                    Atom::Bool(term) => self.state.translate_term(term),
                    Atom::Less(a, b) | Atom::Equal(a, b) => {
                        let op = if matches!(test, Atom::Less(..)) {
                            "<"
                        } else {
                            "="
                        };
                        (|| {
                            Ok(SExpr::application(
                                op,
                                vec![self.state.translate_term(a)?, self.state.translate_term(b)?],
                            ))
                        })()
                    }
                };
                let test = match test {
                    Ok(value) => value,
                    Err(error) => return Ok(Err(error)),
                };
                let yes = match self.decision(yes, depth + 1)? {
                    Ok(Some(value)) => value,
                    Ok(None) => return Ok(Ok(None)),
                    Err(error) => return Ok(Err(error)),
                };
                let no = match self.decision(no, depth + 1)? {
                    Ok(Some(value)) => value,
                    Ok(None) => return Ok(Ok(None)),
                    Err(error) => return Ok(Err(error)),
                };
                Ok((
                    SExpr::application("ite", vec![test.clone(), yes.0, no.0]),
                    SExpr::application("ite", vec![test, yes.1, no.1]),
                ))
            }
        };
        let value = match value {
            Ok(value) => value,
            Err(error) => return Ok(Err(error)),
        };
        let name = self.state.fresh_name();
        let domain_name = self.state.fresh_name();
        let reference = (SExpr::atom(name.clone()), SExpr::atom(domain_name.clone()));
        self.bindings.push((name, value.0));
        self.bindings.push((domain_name, value.1));
        self.decisions.insert(Arc::as_ptr(body), reference.clone());
        Ok(Ok(Some(reference)))
    }
}

fn emit(
    summary: Arc<Summary>,
    definition: &BackendDefinition,
    state: &mut TranslationState,
    remaining: &mut usize,
    text: &mut usize,
) -> Stoppable<Result<bool, TranslationError>> {
    stop::check()?;
    if !summary.domain_total {
        // Domain graphs also observe strict arguments of nested helper calls. Their source
        // terms were not present in the original caller query, so prepare those canonical
        // child-domain plans before translating the shared body under its formal parameters.
        let domains = summary
            .domains
            .keys()
            .cloned()
            .map(Predicate::Ceil)
            .collect::<Vec<_>>();
        super::super::functional::prepare(definition, state, &[], &Substitution::new(), &domains)?;
    }
    let previous_exactness = state.exactness;
    state.exactness = Exactness::Exact;
    let previous_bound = state.bound_variables.len();
    let mut parameters = Vec::new();
    for parameter in &summary.parameters {
        stop::check()?;
        let name = state.fresh_name();
        let sort = match prelude_smt_sort(&parameter.sort) {
            Ok(sort) => sort,
            Err(error) => return Ok(Err(error)),
        };
        parameters.push(SExpr::List(vec![
            SExpr::atom(name.clone()),
            SExpr::atom(sort),
        ]));
        state.bound_variables.push((parameter.clone(), name));
    }
    state.shared_terms = Some(SharedTerms::default());
    let mut body = Body {
        state,
        decisions: FxHashMap::default(),
        domains: &summary.domains,
        formal: &summary.formal,
        bindings: Vec::new(),
        remaining,
    };
    let result = body.decision(&summary.body, 0)?;
    let decision_bindings = body.bindings;
    let fallback = if summary.declared_total && !summary.domain_total {
        // The current summary is not installed yet: this is the ordinary pure total UF,
        // not a recursive use of the source body outside its justified safe region.
        match state.translate_term(&summary.formal) {
            Ok(value) => Some(value),
            Err(error) => return Ok(Err(error)),
        }
    } else {
        None
    };
    let scope = state.shared_terms.take().expect("summary body scope");
    state.bound_variables.truncate(previous_bound);
    let exactness = state.exactness;
    state.exactness = previous_exactness.and(exactness);
    let result = match result {
        Ok(Some(result)) => result,
        Ok(None) => return Ok(Ok(false)),
        Err(error) => return Ok(Err(error)),
    };
    let (value, domain) = result;
    let value = if let Some(fallback) = fallback {
        SExpr::application("ite", vec![domain.clone(), value, fallback])
    } else {
        value
    };
    let bindings = scope
        .bindings
        .into_iter()
        .chain(decision_bindings)
        .collect::<Vec<_>>();
    let value = word::scalar_bindings(bindings.clone(), value)?;
    let domain = word::scalar_bindings(bindings, domain)?;
    let name = state.fresh_name();
    let domain_name = (!summary.domain_total).then(|| state.fresh_name());
    let sort = match prelude_smt_sort(&summary.key.result) {
        Ok(sort) => sort,
        Err(error) => return Ok(Err(error)),
    };
    // `define-fun` is a parser macro in Z3: distinct arguments in a dependency diamond can
    // expand exponentially before a solver check (and its limits) begins. This definition
    // keeps function applications as AST nodes during loading. The admitted source graph is
    // acyclic; using this SMT mechanism does not admit recursive K helpers.
    let definition = SExpr::application(
        "define-fun-rec",
        vec![
            SExpr::atom(name.clone()),
            SExpr::List(parameters.clone()),
            SExpr::atom(sort),
            value,
        ],
    );
    let domain_definition = domain_name.as_ref().map(|name| {
        SExpr::application(
            "define-fun-rec",
            vec![
                SExpr::atom(name.clone()),
                SExpr::List(parameters),
                SExpr::atom("Bool"),
                domain,
            ],
        )
    });
    if !word::fits_text(&definition, text)? {
        return Ok(Ok(false));
    }
    if let Some(domain) = &domain_definition
        && !word::fits_text(domain, text)?
    {
        return Ok(Ok(false));
    }
    state.derived_definitions.push(definition.to_string());
    if let Some(domain) = domain_definition {
        state.derived_definitions.push(domain.to_string());
    }
    state.summaries.insert(
        summary.key.clone(),
        Reading {
            summary,
            name,
            domain_name,
            exactness,
        },
    );
    Ok(Ok(true))
}

pub(in crate::smt) fn prepare(
    source: &Source,
    state: &mut TranslationState,
    known: &[Predicate],
    substitution: &Substitution,
    checked: &[Predicate],
) -> Stoppable<Result<(), TranslationError>> {
    stop::check()?;
    if state.congruence.is_none() {
        return Ok(Ok(()));
    }
    let Some(calls) = calls(known, substitution, checked)? else {
        return Ok(Ok(()));
    };
    let mut catalog = Catalog::new(&source.0);
    for call in calls {
        stop::check()?;
        if state.eligible_operand(call) {
            let _ = catalog.admit(call)?;
        }
    }
    // The catalog's accepted graph is acyclic. Emit a key only after every dependency has
    // successfully emitted, rather than replacing a refused dependency with an invented body.
    let mut pending = catalog.accepted;
    let mut remaining = WORK;
    let mut text = TEXT;
    while !pending.is_empty() && remaining > 0 {
        stop::check()?;
        remaining -= 1;
        let ready = pending
            .iter()
            .find(|(_, summary)| {
                summary
                    .dependencies
                    .iter()
                    .all(|key| state.summaries.contains_key(key))
            })
            .map(|(key, _)| key.clone());
        let Some(key) = ready else {
            break;
        };
        let summary = pending.remove(&key).expect("ready summary");
        match emit(summary, &source.0, state, &mut remaining, &mut text)? {
            Ok(true) => {}
            Ok(false) => break,
            Err(error) => return Ok(Err(error)),
        }
    }
    Ok(Ok(()))
}
