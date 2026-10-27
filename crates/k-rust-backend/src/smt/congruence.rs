//! Bounded sufficient conditions for positive map equalities in pure application contexts.
//!
//! Equal arguments imply equal applications; the converse is never assumed. Scalar values
//! remain whole observations/expressions, since equal reads do not require equal source maps.
//! Only a proof of the sufficient conjunction or independent proofs of every condition may
//! replace the original query.
//! Each map equality also retains the definedness of both original sides: raw SMT value
//! equalities alone do not establish the domains of their partial source operands.
//! Every other result uses ordinary preparation, including finite map extensional consequences.

use super::{SmtPrelude, TranslationState};
use crate::{
    rule::Predicate,
    stop::{self, Stoppable},
    term::{TermKind, equal_terms_bounded},
};
use k_rust_kore::names::BuiltinSort;
use rustc_hash::FxHashSet;
use std::sync::Arc;

const WORK: usize = 4096;
pub(super) const GOALS: usize = 32;

#[expect(
    clippy::wildcard_enum_match_arm,
    reason = "Unmatched forms retain the original equality in this sufficient proof attempt"
)]
/// ```toml algorithm-site
/// id = "backend.smt.check"
/// role = "part"
/// sites = ["sufficient"]
/// ```
pub(super) fn sufficient(
    prelude: &SmtPrelude,
    checked: &[Predicate],
) -> Stoppable<Option<Vec<Predicate>>> {
    stop::check()?;
    let Some(source) = &prelude.source else {
        return Ok(None);
    };
    let definition = source.definition();
    let Some(policy) = &prelude.congruence else {
        return Ok(None);
    };
    if checked.len() > GOALS {
        return Ok(None);
    }
    let mut state = TranslationState::new();
    state.congruence = Some(policy.clone());
    let mut remaining = WORK;
    let mut goals = Vec::new();
    let mut predicates = checked.iter().collect::<Vec<_>>();
    let mut admitted = FxHashSet::default();
    let mut changed = false;
    while let Some(predicate) = predicates.pop() {
        stop::check()?;
        if remaining == 0 {
            return Ok(None);
        }
        remaining -= 1;
        if let Predicate::And(parts) = predicate {
            if parts.len() + predicates.len() + goals.len() > GOALS {
                return Ok(None);
            }
            predicates.extend(parts.iter());
            continue;
        }
        let map_pair = match predicate {
            Predicate::Equals(a, b)
                if a.sort() == b.sort() && definition.map_operations(&a.sort()).is_some() =>
            {
                Some((a, b))
            }
            _ => None,
        };
        let Some((left, right)) = map_pair else {
            goals.push(predicate.clone());
            if goals.len() > GOALS {
                return Ok(None);
            }
            continue;
        };
        goals.push(Predicate::Ceil(left.clone()));
        goals.push(Predicate::Ceil(right.clone()));
        if goals.len() > GOALS {
            return Ok(None);
        }
        // Borrowed graph identity bounds admission even for separately allocated equal DAGs.
        // Do not send an unbounded term graph through a value-keyed eligibility memo first.
        let mut terms = vec![left, right];
        while let Some(term) = terms.pop() {
            stop::check()?;
            if remaining == 0 {
                return Ok(None);
            }
            remaining -= 1;
            if !admitted.insert(term.node_address()) {
                continue;
            }
            if !crate::rewrite::functional_pattern_node(term) {
                return Ok(None);
            }
            let arity = match term.kind() {
                TermKind::Application {
                    symbol,
                    arguments,
                    sort_arguments,
                } => {
                    if arguments.len() > remaining.saturating_sub(terms.len())
                        || sort_arguments.len() > remaining
                    {
                        return Ok(None);
                    }
                    if symbol.attributes.binder
                        || symbol.attributes.macro_or_alias
                        || policy.effects.contains(symbol.name.as_ref())
                        || !definition
                            .symbols()
                            .get(&symbol.name)
                            .is_some_and(|owned| Arc::ptr_eq(owned, symbol))
                        || state.functional_head_rank(term).is_none()
                    {
                        return Ok(None);
                    }
                    arguments.len()
                }
                TermKind::Injection { .. } => {
                    if state.functional_head_rank(term).is_none() {
                        return Ok(None);
                    }
                    1
                }
                TermKind::Map { entries, rest, .. } => entries
                    .len()
                    .saturating_mul(2)
                    .saturating_add(usize::from(rest.is_some())),
                TermKind::List { heads, rest, .. } => heads.len().saturating_add(
                    rest.as_ref()
                        .map_or(0, |(_, tails)| tails.len().saturating_add(1)),
                ),
                TermKind::Set { elements, rest, .. } => {
                    elements.len().saturating_add(usize::from(rest.is_some()))
                }
                TermKind::Variable(_) | TermKind::DomainValue { .. } => 0,
                TermKind::And(..) => return Ok(None),
            };
            if arity > remaining.saturating_sub(terms.len()) {
                return Ok(None);
            }
            terms.extend(crate::term::immediate_children(term.kind()));
        }
        let mut pairs = vec![(left, right)];
        let mut seen = FxHashSet::default();
        while let Some((a, b)) = pairs.pop() {
            stop::check()?;
            match equal_terms_bounded(a, b, &mut remaining) {
                Some(true) => continue,
                Some(false) => {}
                None => return Ok(None),
            }
            if !seen.insert((a.node_address(), b.node_address())) {
                continue;
            }
            let scalar =
                a.sort().is_builtin(BuiltinSort::Int) || a.sort().is_builtin(BuiltinSort::Bool);
            let children = if scalar {
                None
            } else {
                match (a.kind(), b.kind()) {
                    (
                        TermKind::Application {
                            symbol: x,
                            sort_arguments: sx,
                            arguments: ax,
                        },
                        TermKind::Application {
                            symbol: y,
                            sort_arguments: sy,
                            arguments: ay,
                        },
                    ) if Arc::ptr_eq(x, y) && sx == sy && ax.len() == ay.len() => {
                        Some(ax.iter().zip(ay).collect::<Vec<_>>())
                    }
                    (
                        TermKind::Injection {
                            source: sx,
                            target: tx,
                            term: a,
                        },
                        TermKind::Injection {
                            source: sy,
                            target: ty,
                            term: b,
                        },
                    ) if sx == sy && tx == ty => Some(vec![(a, b)]),
                    _ => None,
                }
            };
            if let Some(children) = children {
                if children.len() > remaining.saturating_sub(pairs.len()) {
                    return Ok(None);
                }
                changed = true;
                pairs.extend(children);
            } else {
                goals.push(Predicate::Equals(a.clone(), b.clone()));
                if goals.len() > GOALS {
                    return Ok(None);
                }
            }
        }
    }
    // Empty/reflexive checks keep the ordinary prelude/query handling. A returned plan is
    // strictly smaller in its map contexts, so independent checks cannot recreate this plan.
    Ok((changed && !goals.is_empty()).then_some(goals))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        definition::BackendDefinition,
        smt::{SmtSolver, Validity, Z3Solver},
        stop::{CancellationToken, Stop, StopCause},
        substitution::Substitution,
        term::{Sort, Term, Variable},
    };
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    const SOURCE: &str = r#"[] module MAIN
      hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
      hooked-sort SortBool{} [hook{}("BOOL.Bool"),hasDomainValues{}()]
      sort SortKItem{} []
      hooked-sort SortMap{} [hook{}("MAP.Map"),unit{}(unit{}()),element{}(item{}()),concat{}(concat{}())]
      hooked-symbol unit{}() : SortMap{} [function{}(),total{}(),hook{}("MAP.unit")]
      hooked-symbol item{}(SortKItem{},SortKItem{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.element")]
      hooked-symbol concat{}(SortMap{},SortMap{}) : SortMap{} [function{}(),hook{}("MAP.concat"),assoc{}(),comm{}()]
      hooked-symbol put{}(SortMap{},SortKItem{},SortKItem{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.update")]
      hooked-symbol get{}(SortMap{},SortKItem{}) : SortKItem{} [function{}(),hook{}("MAP.lookup")]
      hooked-symbol member{}(SortKItem{},SortMap{}) : SortBool{} [function{}(),total{}(),hook{}("MAP.in_keys")]
      hooked-symbol remove{}(SortMap{},SortKItem{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.remove")]
      symbol inj{From,To}(From) : To [sortInjection{}()]
      symbol context{}(SortMap{},SortInt{}) : SortMap{} [function{}(),total{}()]
      symbol partial{}(SortMap{},SortInt{}) : SortMap{} [function{}()]
      symbol observe{}(SortMap{}) : SortInt{} [function{}(),total{}()]
      symbol pair{}(SortInt{},SortInt{}) : SortInt{} [function{}(),total{}()]
      symbol effect{}() : SortInt{} [function{}(),total{}(),impure{}()]
      axiom{R} \exists{R}(V:SortKItem{},\equals{SortKItem{},R}(V:SortKItem{},inj{SortInt{},SortKItem{}}(X:SortInt{}))) [subsort{SortInt{},SortKItem{}}()]
    endmodule []"#;
    fn definition() -> BackendDefinition {
        BackendDefinition::internalize(&parse_definition(SOURCE).unwrap(), "MAIN").unwrap()
    }
    fn term(d: &BackendDefinition, s: &str) -> Term {
        d.internalize_term(&parse_pattern(s).unwrap(), &[]).unwrap()
    }
    fn equality(d: &BackendDefinition, a: &str, b: &str) -> Predicate {
        Predicate::Equals(term(d, a), term(d, b))
    }
    fn plan(d: &BackendDefinition, checked: &[Predicate]) -> Option<Vec<Predicate>> {
        sufficient(&SmtPrelude::from_definition(d).unwrap(), checked)
            .map_err(Stop::into_cause)
            .unwrap()
    }

    #[test]
    fn scalar_observations_stay_whole_and_only_positive_contexts_are_split() {
        let d = definition();
        let check = equality(
            &d,
            "context{}(M:SortMap{},observe{}(A:SortMap{}))",
            "context{}(M:SortMap{},observe{}(B:SortMap{}))",
        );
        let expected = equality(&d, "observe{}(A:SortMap{})", "observe{}(B:SortMap{})");
        assert_eq!(
            plan(&d, std::slice::from_ref(&check)),
            Some(vec![
                Predicate::Ceil(term(&d, "context{}(M:SortMap{},observe{}(A:SortMap{}))")),
                Predicate::Ceil(term(&d, "context{}(M:SortMap{},observe{}(B:SortMap{}))")),
                expected.clone(),
            ])
        );
        assert!(plan(&d, &[Predicate::Not(Arc::new(check.clone()))]).is_none());
        let bound = Variable::new("X", Sort::simple("SortMap"));
        assert!(plan(&d, &[Predicate::Exists(bound, Arc::new(check.clone()))]).is_none());
        let solver = Z3Solver::new(&d).unwrap();
        let before = k_rust_kore::measure::snapshot();
        assert_eq!(
            solver.check_predicates(&[expected], &Substitution::new(), &[check]),
            Ok(Ok(Validity::Valid))
        );
        assert_eq!(
            k_rust_kore::measure::snapshot()
                .delta(&before)
                .get(k_rust_kore::measure::Counter::SmtPreparedQueries),
            1,
            "the sufficient query retains both domains and the whole scalar observation"
        );
    }

    #[test]
    fn congruent_partial_maps_still_require_an_original_domain() {
        let d = definition();
        let left = term(&d, "partial{}(M:SortMap{},X:SortInt{})");
        let right = term(&d, "partial{}(M:SortMap{},Y:SortInt{})");
        let check = Predicate::Equals(left.clone(), right.clone());
        let goals = plan(&d, std::slice::from_ref(&check)).unwrap();
        assert!(goals.contains(&Predicate::Ceil(left.clone())));
        assert!(goals.contains(&Predicate::Ceil(right.clone())));
        let equal = equality(&d, "X:SortInt{}", "Y:SortInt{}");
        let solver = Z3Solver::new(&d).unwrap();
        assert_eq!(
            solver.check_predicates(
                &[
                    equal.clone(),
                    Predicate::Not(Arc::new(Predicate::Ceil(left.clone())))
                ],
                &Substitution::new(),
                &[
                    Predicate::Ceil(left.clone()),
                    Predicate::Ceil(right),
                    check.clone(),
                ],
            ),
            Ok(Ok(Validity::Refuted))
        );
        assert_eq!(
            solver.check_predicates(
                &[equal, Predicate::Ceil(left)],
                &Substitution::new(),
                &[check],
            ),
            Ok(Ok(Validity::Valid))
        );
    }

    #[test]
    fn a_refuted_sufficient_condition_does_not_refute_the_original_equality() {
        let d = definition();
        let check = equality(
            &d,
            "context{}(M:SortMap{},\\dv{SortInt{}}(\"1\"))",
            "context{}(M:SortMap{},\\dv{SortInt{}}(\"2\"))",
        );
        assert_eq!(
            Z3Solver::new(&d)
                .unwrap()
                .check_predicates(&[], &Substitution::new(), &[check]),
            Ok(Ok(Validity::Contingent))
        );
        let check = equality(
            &d,
            "put{}(put{}(M:SortMap{},inj{SortInt{},SortKItem{}}(\\dv{SortInt{}}(\"1\")),inj{SortInt{},SortKItem{}}(\\dv{SortInt{}}(\"3\"))),inj{SortInt{},SortKItem{}}(\\dv{SortInt{}}(\"2\")),inj{SortInt{},SortKItem{}}(\\dv{SortInt{}}(\"4\")))",
            "put{}(put{}(M:SortMap{},inj{SortInt{},SortKItem{}}(\\dv{SortInt{}}(\"2\")),inj{SortInt{},SortKItem{}}(\\dv{SortInt{}}(\"4\"))),inj{SortInt{},SortKItem{}}(\\dv{SortInt{}}(\"1\")),inj{SortInt{},SortKItem{}}(\\dv{SortInt{}}(\"3\")))",
        );
        assert_eq!(
            Z3Solver::new(&d)
                .unwrap()
                .check_predicates(&[], &Substitution::new(), &[check]),
            Ok(Ok(Validity::Valid))
        );
    }

    #[test]
    fn foreign_heads_and_malformed_ranks_do_not_supply_source_congruence() {
        let d = definition();
        let other = definition();
        let left = term(&other, "context{}(M:SortMap{},X:SortInt{})");
        let right = term(&d, "context{}(M:SortMap{},Y:SortInt{})");
        assert!(plan(&d, &[Predicate::Equals(left, right.clone())]).is_none());
        let malformed = Term::application(
            d.symbols()["context"].clone(),
            vec![],
            vec![term(&d, "M:SortMap{}"), term(&d, "N:SortMap{}")],
        );
        assert!(plan(&d, &[Predicate::Equals(malformed, right)]).is_none());
    }

    #[test]
    fn effects_large_graphs_and_cancelled_requests_decline_or_stop_the_attempt() {
        let d = definition();
        let effect = equality(
            &d,
            "context{}(M:SortMap{},effect{}())",
            "context{}(M:SortMap{},\\dv{SortInt{}}(\"0\"))",
        );
        assert!(plan(&d, &[effect]).is_none());
        let mut a = term(&d, "M:SortMap{}");
        let mut b = term(&d, "N:SortMap{}");
        let head = d.symbols()["context"].clone();
        let zero = Term::int(0);
        for _ in 0..WORK + 1 {
            a = Term::application(head.clone(), vec![], vec![a, zero.clone()]);
            b = Term::application(head.clone(), vec![], vec![b, zero.clone()]);
        }
        assert!(plan(&d, &[Predicate::Equals(a, b)]).is_none());
        let token = CancellationToken::new();
        token.cancel();
        assert_eq!(
            token
                .scope(|| sufficient(&SmtPrelude::from_definition(&d).unwrap(), &[]))
                .map_err(Stop::into_cause),
            Err(StopCause::Cancelled)
        );
    }
}
