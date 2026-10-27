//! Query-local readings of pure functional values and their source domains.
//!
//! A value UF totalizes a partial function without asserting that it exists. Its domain UF
//! names only the unresolved head obligation; canonical ceil rules and strict child domains
//! retain source conditions and every original argument obligation. Domain lets are local to a predicate's
//! lexical scope, so neither shared DAGs nor quantifiers duplicate or capture their meanings.

use std::collections::{BTreeMap, BTreeSet};

use super::{SExpr, TranslationError, TranslationState};
use crate::{
    rule::Predicate,
    term::{FunctionType, SymbolType, Term, TermKind},
};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(super) struct SharedDomains {
    values: BTreeMap<Term, SExpr>,
    active: BTreeSet<Term>,
    bindings: Vec<(String, SExpr)>,
}

impl SharedDomains {
    pub(super) fn bind(self, mut body: SExpr) -> SExpr {
        for (name, value) in self.bindings.into_iter().rev() {
            body = SExpr::List(vec![
                SExpr::atom("let"),
                SExpr::List(vec![SExpr::List(vec![SExpr::atom(name), value])]),
                body,
            ]);
        }
        body
    }
}

impl TranslationState {
    pub(super) fn translate_domain(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
        if self.congruence.is_some() && term.attributes().ceil_free() {
            // Eliminating a domain must not turn an uninterpreted input carrier into
            // an exact model query merely because its variable no longer needs a value.
            if term.attributes().variables.iter().any(|variable| {
                !super::sort_denotation(&variable.sort)
                    .is_ok_and(|sort| sort.exactness() == super::Exactness::Exact)
            }) {
                self.approximate(super::Exactness::Approximate);
            }
            return Ok(SExpr::atom("true"));
        }
        let original = Predicate::Ceil(term.clone());
        let Some(plan) = self.domains.get(term).cloned() else {
            return Ok(self.abstract_predicate(&original));
        };
        let scope = self
            .shared_domains
            .as_mut()
            .expect("predicate domain scope");
        if let Some(value) = scope.values.get(term) {
            return Ok(value.clone());
        }
        // Source ceil equations can be recursive. A cycle or a deep source graph retains
        // an opaque atom, rather than inventing totality or unboundedly expanding it.
        if scope.active.len() >= 128 || !scope.active.insert(term.clone()) {
            return Ok(self.abstract_predicate(&original));
        }
        let result = (|| {
            let mut parts = Vec::new();
            for predicate in plan.iter() {
                if *predicate == original {
                    parts.push(self.translate_domain_head(term)?);
                } else {
                    parts.push(self.translate_predicate(predicate)?);
                }
            }
            let value = match parts.as_slice() {
                [] => SExpr::atom("true"),
                [part] => part.clone(),
                _ => SExpr::application("and", parts),
            };
            // A source rule may decide f(0)'s domain while leaving f(X)'s unresolved.
            // Connect the decided instance to the same head UF, under the original
            // argument domains, so X=0 transports that source fact as well.
            if !plan.contains(&original)
                && let TermKind::Application {
                    symbol, arguments, ..
                } = term.kind()
                && symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial)
                && self.functional_head(term).is_some()
            {
                let mut argument_domains = Vec::new();
                for argument in arguments {
                    argument_domains.push(self.translate_domain(argument)?);
                }
                let head = self.translate_domain_head(term)?;
                let fact = SExpr::application(
                    "=>",
                    vec![
                        SExpr::application("and", argument_domains),
                        SExpr::application("=", vec![head, value.clone()]),
                    ],
                );
                // These are source consequences, not checked obligations. Close their
                // lexical lets and binders before adding them to the query's known facts.
                let mut fact = self
                    .shared_domains
                    .as_ref()
                    .expect("active domain scope")
                    .clone()
                    .bind(fact);
                for (variable, name) in self.bound_variables.clone().into_iter().rev() {
                    let sort = self.smt_sort(&variable.sort)?;
                    fact = SExpr::List(vec![
                        SExpr::atom("forall"),
                        SExpr::List(vec![SExpr::List(vec![
                            SExpr::atom(name),
                            SExpr::atom(sort),
                        ])]),
                        fact,
                    ]);
                }
                self.domain_facts.push(fact);
            }
            Ok(value)
        })();
        let scope = self.shared_domains.as_mut().expect("active domain scope");
        scope.active.remove(term);
        let value = result?;
        if matches!(value, SExpr::Atom(_)) {
            scope.values.insert(term.clone(), value.clone());
            return Ok(value);
        }
        let name = self.fresh_name();
        let reference = SExpr::atom(name.clone());
        let scope = self.shared_domains.as_mut().expect("active domain scope");
        scope.bindings.push((name, value));
        scope.values.insert(term.clone(), reference.clone());
        Ok(reference)
    }

    fn translate_domain_head(&mut self, term: &Term) -> Result<SExpr, TranslationError> {
        let Some(head) = self.functional_head(term) else {
            return Ok(self.abstract_predicate(&Predicate::Ceil(term.clone())));
        };
        self.approximate(super::Exactness::Approximate);
        let name = match self.domain_functions.get(&head) {
            Some(name) => name.clone(),
            None => {
                let name = self.fresh_name();
                self.domain_functions.insert(head, name.clone());
                name
            }
        };
        let arguments = crate::deferred::children(term)
            .into_iter()
            .map(|arg| self.translate_term(arg))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(if arguments.is_empty() {
            SExpr::atom(name)
        } else {
            SExpr::application(name, arguments)
        })
    }
}

/// Derive source predicates before translation, with no query names or caller facts in them.
/// An unsupported operand or exhausted construction budget keeps its previous opaque reading.
#[cfg(any(feature = "z3", test))]
pub(super) fn prepare(
    definition: &crate::definition::BackendDefinition,
    state: &mut TranslationState,
    known: &[Predicate],
    substitution: &crate::substitution::Substitution,
    checked: &[Predicate],
) -> crate::stop::Stoppable<()> {
    use crate::{
        definedness::{apply_ceil_equation, request_definedness},
        stop,
    };

    let mut remaining = 16_384_usize;
    stop::check()?;
    if known
        .len()
        .saturating_add(checked.len())
        .saturating_add(substitution.len())
        > remaining
    {
        return Ok(());
    }
    let mut predicates = known.iter().chain(checked).cloned().collect::<Vec<_>>();
    let mut candidates = Vec::new();
    // Substituted terms can contribute domains reached from a checked partial application.
    candidates.extend(substitution.values().cloned());
    let mut seen = BTreeSet::new();
    while !predicates.is_empty() || !candidates.is_empty() {
        stop::check()?;
        if remaining == 0 {
            break;
        }
        remaining -= 1;
        if let Some(predicate) = predicates.pop() {
            match predicate {
                Predicate::Ceil(term) | Predicate::Defined(term) => candidates.push(term),
                Predicate::Not(p) | Predicate::Exists(_, p) | Predicate::Forall(_, p) => {
                    predicates.push((*p).clone());
                }
                Predicate::And(parts) | Predicate::Or(parts) => {
                    if parts.len() > remaining {
                        break;
                    }
                    predicates.extend(parts.iter().cloned());
                }
                Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                    predicates.extend([(*a).clone(), (*b).clone()]);
                }
                Predicate::True
                | Predicate::False
                | Predicate::Term(_)
                | Predicate::Equals(..)
                | Predicate::Floor(_)
                | Predicate::In(..)
                | Predicate::Absent(_) => {}
            }
            continue;
        }
        let term = candidates.pop().expect("pending domain candidate");
        if !seen.insert(term.clone()) || !state.eligible_operand(&term) {
            continue;
        }
        let mut plan = match term.kind() {
            TermKind::Application { symbol, .. } if state.functional_head(&term).is_some() => {
                if symbol.attributes.symbol_type == SymbolType::Function(FunctionType::Partial) {
                    match apply_ceil_equation(definition, &term) {
                        Some(conditions)
                            if admit_conditions(state, &conditions, &mut remaining) =>
                        {
                            request_definedness(definition, conditions)
                                .unwrap_or_else(|_| vec![Predicate::Ceil(term.clone())])
                        }
                        Some(_) | None => vec![Predicate::Ceil(term.clone())],
                    }
                } else {
                    Vec::new()
                }
            }
            TermKind::Variable(_) | TermKind::DomainValue { .. } | TermKind::Injection { .. } => {
                Vec::new()
            }
            TermKind::Application { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. }
            | TermKind::And(..) => continue,
        };
        // One head at a time: a full ceil walk here would repeatedly traverse shared
        // operands and can expand a small partial-function DAG exponentially. These
        // operands have already passed purity admission, so applications/injections keep
        // exactly their strict child domains, without evaluating deferred effects.
        for child in crate::deferred::children(&term) {
            if !child.attributes().ceil_free() {
                plan.push(Predicate::Ceil(child.clone()));
            }
        }
        stop::check()?;
        if plan.len() > remaining {
            break;
        }
        predicates.extend(
            plan.iter()
                .filter(|p| **p != Predicate::Ceil(term.clone()))
                .cloned(),
        );
        state.domains.insert(term, plan.into());
    }
    Ok(())
}

/// Bound the tree work of canonical condition conversion before asking it to traverse a
/// shared value DAG. Opaque domain atoms need no value walk; value atoms must be pure.
#[cfg(any(feature = "z3", test))]
fn admit_conditions(
    state: &mut TranslationState,
    conditions: &[Predicate],
    remaining: &mut usize,
) -> bool {
    enum Pending<'a> {
        Predicate(&'a Predicate),
        Term(&'a Term),
    }
    if conditions.len() > *remaining {
        return false;
    }
    let mut pending = conditions
        .iter()
        .map(Pending::Predicate)
        .collect::<Vec<_>>();
    while let Some(node) = pending.pop() {
        if *remaining == 0 {
            return false;
        }
        *remaining -= 1;
        match node {
            Pending::Term(term) => {
                if !state.eligible_operand(term) {
                    return false;
                }
                let children = crate::deferred::children(term);
                if children.len() > *remaining {
                    return false;
                }
                pending.extend(children.into_iter().map(Pending::Term));
            }
            Pending::Predicate(predicate) => match predicate {
                Predicate::Term(t) => pending.push(Pending::Term(t)),
                Predicate::Equals(a, b) => pending.extend([Pending::Term(a), Pending::Term(b)]),
                Predicate::Not(p) | Predicate::Exists(_, p) | Predicate::Forall(_, p) => {
                    pending.push(Pending::Predicate(p));
                }
                Predicate::And(ps) | Predicate::Or(ps) => {
                    if ps.len() > *remaining {
                        return false;
                    }
                    pending.extend(ps.iter().map(Pending::Predicate));
                }
                Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                    pending.extend([Pending::Predicate(a), Pending::Predicate(b)]);
                }
                Predicate::Ceil(t) | Predicate::Defined(t) | Predicate::Floor(t) => {
                    if !state.eligible_operand(t) {
                        return false;
                    }
                }
                Predicate::In(a, b) => {
                    if !state.eligible_operand(a) || !state.eligible_operand(b) {
                        return false;
                    }
                }
                Predicate::True | Predicate::False | Predicate::Absent(_) => {}
            },
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        definition::BackendDefinition,
        smt::{CongruencePolicy, Exactness, translate_query_in_state},
        stop::{CancellationToken, StopCause},
        substitution::Substitution,
    };
    use std::sync::Arc;

    fn definition() -> BackendDefinition {
        let syntax = k_rust_kore::kore::parser::parse_definition(
            r#"[] module MAIN
              hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
              symbol f{}(SortInt{}) : SortInt{} [function{}()]
              symbol effect{}(SortInt{}) : SortInt{} [function{}(),impure{}()]
            endmodule []"#,
        )
        .unwrap();
        BackendDefinition::internalize(&syntax, "MAIN").unwrap()
    }

    #[test]
    fn portable_domains_retain_argument_rank_and_conservative_model_evidence() {
        let definition = definition();
        let term = definition
            .internalize_term(
                &k_rust_kore::kore::parser::parse_pattern("f{}(X:SortInt{})").unwrap(),
                &[],
            )
            .unwrap();
        let checked = [Predicate::Ceil(term)];
        let mut state = TranslationState::new();
        state.congruence = CongruencePolicy::from_definition(&definition).map(Arc::new);
        prepare(&definition, &mut state, &[], &Substitution::new(), &checked).unwrap();
        let (state, declarations, _, _, checked) =
            translate_query_in_state(&[], &Substitution::new(), &checked, state).unwrap();
        assert_eq!(state.exactness(), Exactness::Approximate);
        assert!(declarations.iter().any(|d| d.ends_with("(Int) Bool)")));
        assert!(SExpr::parse(&checked.to_string()).is_ok());
    }

    #[test]
    fn domain_preparation_propagates_a_cancelled_request() {
        let definition = definition();
        let token = CancellationToken::new();
        token.cancel();
        let mut state = TranslationState::new();
        let stopped = token
            .scope(|| prepare(&definition, &mut state, &[], &Substitution::new(), &[]))
            .unwrap_err();
        assert_eq!(stopped.into_cause(), StopCause::Cancelled);
    }
}
