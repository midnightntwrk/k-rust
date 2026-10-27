//! Translate source-checked finite observations while retaining the ordinary value/domain
//! signature. These source consequences are guarded, not asserted caller obligations.

use std::{collections::BTreeMap, sync::Arc};

use super::{SExpr, TranslationError, TranslationState};
use crate::{observation::reading::Reading, rule::Predicate, term::Term};

impl TranslationState {
    pub(super) fn translate_observation(
        &mut self,
        term: &Term,
        reading: &Arc<Reading>,
    ) -> Result<SExpr, TranslationError> {
        // Always keep the original functional interpretation. A source equation about this
        // instance then also transports through opaque equal arguments and higher contexts.
        let original = self.translate_term_node_plain(term)?;
        let value = self.observation_value(reading, &original, &mut BTreeMap::new())?;
        let domain = self.translate_predicate(&Predicate::Ceil(term.clone()))?;
        self.approximate(super::Exactness::Approximate);
        self.record_source_fact(SExpr::application(
            "=>",
            vec![
                domain,
                SExpr::application("=", vec![original.clone(), value]),
            ],
        ))?;
        Ok(original)
    }

    fn observation_value(
        &mut self,
        reading: &Arc<Reading>,
        fallback: &SExpr,
        memo: &mut BTreeMap<usize, SExpr>,
    ) -> Result<SExpr, TranslationError> {
        let key = Arc::as_ptr(reading) as usize;
        if let Some(value) = memo.get(&key) {
            return Ok(value.clone());
        }
        let value = match reading.as_ref() {
            Reading::Leaf(term) => self.translate_term(term)?,
            Reading::Missing => fallback.clone(),
            Reading::If { test, yes, no } => SExpr::application(
                "ite",
                vec![
                    self.translate_predicate(test)?,
                    self.observation_value(yes, fallback, memo)?,
                    self.observation_value(no, fallback, memo)?,
                ],
            ),
        };
        let value = if matches!(value, SExpr::List(_)) {
            if self.shared_terms.is_some() {
                let name = self.fresh_name();
                self.shared_terms
                    .as_mut()
                    .expect("value scope")
                    .bindings
                    .push((name.clone(), value));
                SExpr::atom(name)
            } else {
                value
            }
        } else {
            value
        };
        memo.insert(key, value.clone());
        Ok(value)
    }

    pub(super) fn observation_domain(
        &mut self,
        term: &Term,
        reading: &Arc<Reading>,
    ) -> Result<SExpr, TranslationError> {
        let mut domains = Vec::new();
        // The source state and all original operands stay strict, including overwritten
        // values and both operands of a source state conditional.
        for child in crate::deferred::children(term) {
            domains.push(self.translate_domain(child)?);
        }
        domains.push(self.observation_leaf_domain(reading, &mut BTreeMap::new())?);
        Ok(SExpr::application("and", domains))
    }

    fn observation_leaf_domain(
        &mut self,
        reading: &Arc<Reading>,
        memo: &mut BTreeMap<usize, SExpr>,
    ) -> Result<SExpr, TranslationError> {
        let key = Arc::as_ptr(reading) as usize;
        if let Some(value) = memo.get(&key) {
            return Ok(value.clone());
        }
        let value = match reading.as_ref() {
            Reading::Leaf(term) => self.translate_domain(term)?,
            Reading::Missing => SExpr::atom("false"),
            Reading::If { test, yes, no } => SExpr::application(
                "ite",
                vec![
                    self.translate_predicate(test)?,
                    self.observation_leaf_domain(yes, memo)?,
                    self.observation_leaf_domain(no, memo)?,
                ],
            ),
        };
        let value = if matches!(value, SExpr::List(_)) {
            let name = self.fresh_name();
            self.shared_domains
                .as_mut()
                .expect("domain scope")
                .bindings
                .push((name.clone(), value));
            SExpr::atom(name)
        } else {
            value
        };
        memo.insert(key, value.clone());
        Ok(value)
    }
}

/// Discover plans from all demanded source terms. The additional ceil predicates prepare
/// domains of generated source leaves; they are never added to the query's assumptions.
#[cfg(any(feature = "z3", test))]
pub(super) fn prepare(
    definition: &crate::definition::BackendDefinition,
    state: &mut TranslationState,
    known: &[Predicate],
    substitution: &crate::substitution::Substitution,
    checked: &[Predicate],
) -> crate::stop::Stoppable<Vec<Predicate>> {
    use crate::{observation::reading::Builder, stop};
    use std::collections::BTreeSet;
    let mut remaining = 16_384usize;
    if known
        .len()
        .saturating_add(checked.len())
        .saturating_add(substitution.len())
        > remaining
    {
        return Ok(Vec::new());
    }
    let mut predicates = known.iter().chain(checked).cloned().collect::<Vec<_>>();
    let mut terms = substitution.values().cloned().collect::<Vec<_>>();
    let mut builder = Builder::new(definition);
    let mut seen = BTreeSet::new();
    let mut seen_readings = BTreeSet::new();
    let mut readings = Vec::new();
    let mut domains = Vec::new();
    // Equalities select additional demands only. Even an equality under a negation or a
    // different binder may safely suggest a source-law instance; it is never assumed here.
    let mut aliases = BTreeMap::<Term, Vec<Term>>::new();
    for (variable, value) in substitution {
        stop::check()?;
        remaining -= 1;
        if variable.sort == value.sort() && definition.map_operations(&variable.sort).is_some() {
            let variable = Term::variable(variable.clone());
            aliases
                .entry(variable.clone())
                .or_default()
                .push(value.clone());
            aliases.entry(value.clone()).or_default().push(variable);
        }
    }
    while !terms.is_empty() || !predicates.is_empty() || !readings.is_empty() {
        stop::check()?;
        if remaining == 0 {
            break;
        }
        remaining -= 1;
        if let Some(reading) = readings.pop() {
            let reading: Arc<Reading> = reading;
            if !seen_readings.insert(Arc::as_ptr(&reading) as usize) {
                continue;
            }
            match reading.as_ref() {
                Reading::Leaf(term) => terms.push(term.clone()),
                Reading::Missing => {}
                Reading::If { test, yes, no } => {
                    predicates.push(test.clone());
                    readings.extend([yes.clone(), no.clone()]);
                }
            }
        } else if let Some(predicate) = predicates.pop() {
            match predicate {
                Predicate::Term(t) | Predicate::Ceil(t) | Predicate::Defined(t) => terms.push(t),
                Predicate::Equals(a, b) => {
                    if a.sort() == b.sort() && definition.map_operations(&a.sort()).is_some() {
                        aliases.entry(a.clone()).or_default().push(b.clone());
                        aliases.entry(b.clone()).or_default().push(a.clone());
                    }
                    terms.extend([a, b]);
                }
                Predicate::Not(p) | Predicate::Exists(_, p) | Predicate::Forall(_, p) => {
                    predicates.push((*p).clone())
                }
                Predicate::And(ps) | Predicate::Or(ps) => {
                    if ps.len() > remaining {
                        break;
                    }
                    predicates.extend(ps.iter().cloned());
                }
                Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                    predicates.extend([(*a).clone(), (*b).clone()])
                }
                Predicate::True
                | Predicate::False
                | Predicate::Floor(_)
                | Predicate::In(..)
                | Predicate::Absent(_) => {}
            }
        } else if let Some(term) = terms.pop() {
            if !seen.insert(term.clone()) {
                continue;
            }
            if let Some(reading) = builder.of(&term)? {
                readings.push(reading.clone());
                state.observations.insert(term.clone(), reading);
            } else if let crate::term::TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            } = term.kind()
            {
                let position = match symbol.attributes.hook.as_deref() {
                    Some("MAP.lookup") if arguments.len() == 2 => Some(0),
                    Some("MAP.in_keys") if arguments.len() == 2 => Some(1),
                    _ => None,
                };
                if let Some(position) = position {
                    let mut pending = vec![arguments[position].clone()];
                    let mut reached = BTreeSet::new();
                    let mut demands = Vec::new();
                    while let Some(map) = pending.pop() {
                        stop::check()?;
                        if !reached.insert(map.clone()) {
                            continue;
                        }
                        let Some(next) = aliases.get(&map) else {
                            continue;
                        };
                        if next.len() > remaining {
                            break;
                        }
                        remaining -= next.len();
                        for alternative in next {
                            if alternative != &arguments[position] {
                                let mut arguments = arguments.clone();
                                arguments[position] = alternative.clone();
                                let source =
                                    Term::application(symbol.clone(), *sort_arguments, arguments);
                                if let Some(reading) = builder.of(&source)? {
                                    state.observations.insert(source.clone(), reading);
                                    terms.push(source.clone());
                                    demands.push(source);
                                }
                            }
                            pending.push(alternative.clone());
                        }
                    }
                    if !demands.is_empty() {
                        state.observation_demands.insert(term.clone(), demands);
                    }
                }
            }
            let children = crate::deferred::children(&term);
            if children.len() > remaining {
                break;
            }
            terms.extend(children.into_iter().cloned());
            domains.push(Predicate::Ceil(term));
        }
    }
    Ok(domains)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{definition::BackendDefinition, substitution::Substitution};
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    fn source() -> &'static str {
        r#"[] module MAIN
          hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
          hooked-sort SortBool{} [hook{}("BOOL.Bool"),hasDomainValues{}()]
          hooked-sort SortMap{} [hook{}("MAP.Map"),unit{}(unit{}()),element{}(item{}()),concat{}(concat{}())]
          hooked-symbol unit{}() : SortMap{} [function{}(),total{}(),hook{}("MAP.unit")]
          hooked-symbol item{}(SortInt{},SortInt{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.element")]
          hooked-symbol concat{}(SortMap{},SortMap{}) : SortMap{} [function{}(),hook{}("MAP.concat"),assoc{}(),comm{}()]
          hooked-symbol put{}(SortMap{},SortInt{},SortInt{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.update")]
          hooked-symbol get{}(SortMap{},SortInt{}) : SortInt{} [function{}(),hook{}("MAP.lookup")]
          hooked-symbol member{}(SortInt{},SortMap{}) : SortBool{} [function{}(),total{}(),hook{}("MAP.in_keys")]
          hooked-symbol remove{}(SortMap{},SortInt{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.remove")]
          hooked-symbol choose{S}(SortBool{},S,S) : S [function{}(),total{}(),hook{}("KEQUAL.ite"),smt-hook{}("ite")]
          symbol f{}(SortInt{}) : SortInt{} [function{}()]
          symbol effect{}(SortInt{}) : SortInt{} [function{}(),impure{}()]
        endmodule []"#
    }

    fn typed_source() -> String {
        source()
            .replace("item{}(SortInt{},SortInt{})", "item{}(SortKItem{},SortKItem{})")
            .replace("put{}(SortMap{},SortInt{},SortInt{})", "put{}(SortMap{},SortKItem{},SortKItem{})")
            .replace("get{}(SortMap{},SortInt{}) : SortInt{}", "get{}(SortMap{},SortKItem{}) : SortKItem{}")
            .replace("member{}(SortInt{},SortMap{})", "member{}(SortKItem{},SortMap{})")
            .replace("remove{}(SortMap{},SortInt{})", "remove{}(SortMap{},SortKItem{})")
            .replace("endmodule", r#"
              sort SortKItem{} []
              sort SortK{} []
              symbol inj{From,To}(From) : To [sortInjection{}()]
              symbol kseq{}(SortKItem{},SortK{}) : SortK{} [constructor{}()]
              symbol dotk{}() : SortK{} [constructor{}()]
              symbol project{}(SortK{}) : SortInt{} [function{}()]
              axiom{R} \exists{R}(V:SortKItem{},\equals{SortKItem{},R}(V:SortKItem{},inj{SortInt{},SortKItem{}}(X:SortInt{}))) [subsort{SortInt{},SortKItem{}}()]
              axiom{R} \implies{R}(\and{R}(\top{R}(),\and{R}(\in{SortK{},R}(X:SortK{},kseq{}(inj{SortInt{},SortKItem{}}(Y:SortInt{}),dotk{}())),\top{R}())),
                \equals{SortInt{},R}(project{}(X:SortK{}),\and{SortInt{}}(Y:SortInt{},\top{SortInt{}}()))) []
              axiom{R} \implies{R}(\top{R}(),\equals{R,R}(\ceil{SortInt{},R}(project{}(X:SortK{})),
                \exists{R}(Y:SortInt{},\equals{SortK{},R}(X:SortK{},kseq{}(inj{SortInt{},SortKItem{}}(Y:SortInt{}),dotk{}()))))) []
              axiom{R} \implies{R}(\ceil{SortInt{},R}(project{}(Z:SortK{})),
                \equals{SortK{},R}(kseq{}(inj{SortInt{},SortKItem{}}(project{}(Z:SortK{})),dotk{}()),\and{SortK{}}(Z:SortK{},\top{SortK{}}()))) [simplification{}()]
            endmodule"#)
    }

    #[test]
    fn canonical_map_domain_rows_are_checked_without_rejecting_the_compiler_contract() {
        let row = r#"axiom{R} \implies{R}(\top{R}(),\equals{R,R}(
          \ceil{SortMap{},R}(concat{}(item{}(@K:SortInt{},@V:SortInt{}),@M:SortMap{})),
          \and{R}(\equals{SortBool{},R}(member{}(@K:SortInt{},@M:SortMap{}),\dv{SortBool{}}("false")),\ceil{SortInt{},R}(@V:SortInt{})))) []
          endmodule"#;
        let text = source().replace("endmodule", row);
        let definition = definition(&text);
        let sort = crate::term::Sort::simple("SortMap");
        assert!(definition.map_operations(&sort).is_some());
        let changed = text.replace(r#"\dv{SortBool{}}("false")"#, r#"\dv{SortBool{}}("true")"#);
        assert!(self::definition(&changed).map_operations(&sort).is_none());
        let extra = text.replace("endmodule",r#"axiom{R} \implies{R}(\top{R}(),\equals{R,R}(\ceil{SortMap{},R}(concat{}(A:SortMap{},B:SortMap{})),\top{R}())) [] endmodule"#);
        assert!(self::definition(&extra).map_operations(&sort).is_none());
    }

    fn definition(source: &str) -> BackendDefinition {
        BackendDefinition::internalize(&parse_definition(source).unwrap(), "MAIN").unwrap()
    }

    fn term(definition: &BackendDefinition, text: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(text).unwrap(), &[])
            .unwrap()
    }

    #[test]
    fn source_views_validate_operations_and_keep_alias_choices() {
        let definition = definition(source());
        let source = term(
            &definition,
            "get{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),Q:SortInt{})",
        );
        let mut builder = crate::observation::reading::Builder::new(&definition);
        let reading = builder.of(&source).unwrap().unwrap();
        let Reading::If { test, yes, no } = reading.as_ref() else {
            panic!("unknown alias must stay guarded")
        };
        assert_eq!(
            *test,
            Predicate::Equals(
                term(&definition, "Q:SortInt{}"),
                term(&definition, "K:SortInt{}")
            )
        );
        assert_eq!(
            yes.as_ref(),
            &Reading::Leaf(term(&definition, "V:SortInt{}"))
        );
        assert_eq!(
            no.as_ref(),
            &Reading::Leaf(term(&definition, "get{}(M:SortMap{},Q:SortInt{})"))
        );
        assert!(Arc::ptr_eq(
            &reading,
            &builder.of(&source).unwrap().unwrap()
        ));
        let effect = term(
            &definition,
            "get{}(put{}(M:SortMap{},K:SortInt{},effect{}(V:SortInt{})),K:SortInt{})",
        );
        assert!(builder.of(&effect).unwrap().is_none());
        let checked = [Predicate::Ceil(source)];
        let mut state = TranslationState::new();
        state.congruence =
            super::super::CongruencePolicy::from_definition(&definition).map(Arc::new);
        let extra = prepare(&definition, &mut state, &[], &Substitution::new(), &checked).unwrap();
        super::super::functional::prepare(
            &definition,
            &mut state,
            &extra,
            &Substitution::new(),
            &checked,
        )
        .unwrap();
        let (state, declarations, _, _, checked) =
            super::super::translate_query_in_state(&[], &Substitution::new(), &checked, state)
                .unwrap();
        assert_eq!(state.exactness(), super::super::Exactness::Approximate);
        assert!(!state.domain_facts.is_empty());
        for expression in &declarations {
            assert!(SExpr::parse(expression).is_ok());
        }
        assert!(SExpr::parse(&checked.to_string()).is_ok());
    }

    #[test]
    fn missing_support_and_overridden_source_remain_conservative() {
        let without_member = source()
            .lines()
            .filter(|line| !line.contains("hooked-symbol member"))
            .collect::<Vec<_>>()
            .join("\n");
        let definition = definition(&without_member);
        let get = term(&definition, "get{}(M:SortMap{},K:SortInt{})");
        assert!(crate::observation::maps::lookup_domain(&definition, &get).is_none());
        let wildcard = source().replace("endmodule",r#"axiom{R} \implies{R}(\top{R}(),\equals{SortMap{},R}(X:SortMap{},\and{SortMap{}}(unit{}(),\top{SortMap{}}()))) [simplification{}()] endmodule"#);
        let definition = self::definition(&wildcard);
        assert!(
            definition
                .map_operations(&crate::term::Sort::simple("SortMap"))
                .is_none()
        );
        let impure_unit = source().replace(
            "unit{}() : SortMap{} [function{}(),",
            "unit{}() : SortMap{} [function{}(),impure{}(),",
        );
        let definition = self::definition(&impure_unit);
        assert!(
            definition
                .map_operations(&crate::term::Sort::simple("SortMap"))
                .is_none()
        );
        let unhooked_bool = source().replace(
            r#"hooked-sort SortBool{} [hook{}("BOOL.Bool"),hasDomainValues{}()]"#,
            "sort SortBool{} []",
        );
        let definition = self::definition(&unhooked_bool);
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&term(
                    &definition,
                    "member{}(K:SortInt{},put{}(M:SortMap{},K:SortInt{},V:SortInt{}))"
                ))
                .unwrap()
                .is_none()
        );
        assert!(
            crate::observation::maps::lookup_domain(
                &definition,
                &term(&definition, "get{}(M:SortMap{},K:SortInt{})")
            )
            .is_none()
        );
        let total = source().replace(
            "get{}(SortMap{},SortInt{}) : SortInt{} [function{}(),",
            "get{}(SortMap{},SortInt{}) : SortInt{} [function{}(),total{}(),",
        );
        let definition = self::definition(&total);
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&term(
                    &definition,
                    "get{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),K:SortInt{})"
                ))
                .unwrap()
                .is_none()
        );
        let mutated = source().replace("endmodule",r#"axiom{R} \implies{R}(\top{R}(),\equals{SortInt{},R}(get{}(M:SortMap{},K:SortInt{}),\and{SortInt{}}(\dv{SortInt{}}("4"),\top{SortInt{}}()))) [simplification{}()] endmodule"#);
        let definition = self::definition(&mutated);
        let get = term(
            &definition,
            "get{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),K:SortInt{})",
        );
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&get)
                .unwrap()
                .is_none()
        );
        assert!(crate::observation::maps::lookup_domain(&definition, &get).is_none());
    }

    #[cfg(feature = "z3")]
    fn check(
        definition: &BackendDefinition,
        known: &[Predicate],
        checked: Predicate,
    ) -> super::super::Validity {
        use crate::smt::SmtSolver;
        crate::smt::Z3Solver::new(definition)
            .unwrap()
            .check_predicates(known, &Substitution::new(), &[checked])
            .unwrap()
            .unwrap()
    }

    #[cfg(feature = "z3")]
    #[test]
    fn observations_compose_through_opaque_state_aliases_and_partial_contexts() {
        use super::super::Validity;
        let definition = definition(source());
        let put = term(&definition, "put{}(M:SortMap{},K:SortInt{},V:SortInt{})");
        let a = term(&definition, "A:SortMap{}");
        let read = term(&definition, "get{}(A:SortMap{},Q:SortInt{})");
        let known = [
            Predicate::Equals(a, put),
            Predicate::Equals(
                term(&definition, "Q:SortInt{}"),
                term(&definition, "K:SortInt{}"),
            ),
        ];
        assert_eq!(
            check(
                &definition,
                &known,
                Predicate::Equals(read.clone(), term(&definition, "V:SortInt{}"))
            ),
            Validity::Valid
        );
        assert_eq!(
            check(&definition, &known, Predicate::Ceil(read)),
            Validity::Valid
        );
        let checked = Predicate::Equals(
            term(&definition, "f{}(get{}(A:SortMap{},Q:SortInt{}))"),
            term(&definition, "f{}(V:SortInt{})"),
        );
        assert_eq!(check(&definition, &known, checked), Validity::Valid);
        {
            use crate::smt::SmtSolver;
            let substitution = Substitution::from([(
                crate::term::Variable::new("A", crate::term::Sort::simple("SortMap")),
                term(&definition, "put{}(M:SortMap{},K:SortInt{},V:SortInt{})"),
            )]);
            let checked = Predicate::Equals(
                term(&definition, "get{}(A:SortMap{},K:SortInt{})"),
                term(&definition, "V:SortInt{}"),
            );
            assert_eq!(
                crate::smt::Z3Solver::new(&definition)
                    .unwrap()
                    .check_predicates(&[], &substitution, &[checked])
                    .unwrap()
                    .unwrap(),
                Validity::Valid
            );
        }
        let not_equal = [
            Predicate::Not(Arc::new(Predicate::Equals(
                term(&definition, "A:SortMap{}"),
                term(&definition, "put{}(M:SortMap{},K:SortInt{},V:SortInt{})"),
            ))),
            Predicate::Equals(
                term(&definition, "K:SortInt{}"),
                term(&definition, "Q:SortInt{}"),
            ),
        ];
        assert_ne!(
            check(
                &definition,
                &not_equal,
                Predicate::Equals(
                    term(&definition, "get{}(A:SortMap{},Q:SortInt{})"),
                    term(&definition, "V:SortInt{}")
                )
            ),
            Validity::Valid
        );
        let recursive_alias = [Predicate::Equals(
            term(&definition, "M:SortMap{}"),
            term(&definition, "put{}(M:SortMap{},K:SortInt{},V:SortInt{})"),
        )];
        assert_eq!(
            check(
                &definition,
                &recursive_alias,
                Predicate::Equals(
                    term(&definition, "get{}(M:SortMap{},K:SortInt{})"),
                    term(&definition, "V:SortInt{}")
                )
            ),
            Validity::Valid
        );
        // A pure opaque partial function gets forward congruence, never injectivity.
        let known = [Predicate::Equals(
            term(&definition, "f{}(K:SortInt{})"),
            term(&definition, "f{}(Q:SortInt{})"),
        )];
        assert_ne!(
            check(
                &definition,
                &known,
                Predicate::Equals(
                    term(&definition, "K:SortInt{}"),
                    term(&definition, "Q:SortInt{}")
                )
            ),
            Validity::Valid
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn selected_read_domains_retain_strict_state_operands() {
        use super::super::Validity;
        let definition = definition(source());
        let read = term(
            &definition,
            r#"get{}(choose{SortMap{}}(B:SortBool{},put{}(M:SortMap{},K:SortInt{},V:SortInt{}),unit{}()),K:SortInt{})"#,
        );
        let known = [Predicate::Term(term(&definition, "B:SortBool{}"))];
        assert_eq!(
            check(&definition, &known, Predicate::Ceil(read.clone())),
            Validity::Valid
        );
        assert_eq!(
            check(
                &definition,
                &known,
                Predicate::Equals(read, term(&definition, "V:SortInt{}"))
            ),
            Validity::Valid
        );
        let read = term(
            &definition,
            "get{}(put{}(put{}(M:SortMap{},K:SortInt{},f{}(X:SortInt{})),K:SortInt{},V:SortInt{}),K:SortInt{})",
        );
        let undefined = Predicate::Not(Arc::new(Predicate::Ceil(term(
            &definition,
            "f{}(X:SortInt{})",
        ))));
        assert_eq!(
            check(&definition, &[undefined], Predicate::Ceil(read)),
            Validity::Refuted
        );
        let missing = term(
            &definition,
            "get{}(remove{}(M:SortMap{},K:SortInt{}),K:SortInt{})",
        );
        assert_eq!(
            check(&definition, &[], Predicate::Ceil(missing)),
            Validity::Refuted
        );
        let query = crate::smt::SmtPrelude::from_definition(&definition)
            .unwrap()
            .query(
                &[],
                &Substitution::new(),
                &[Predicate::Ceil(term(
                    &definition,
                    "get{}(M:SortMap{},K:SortInt{})",
                ))],
                false,
            )
            .unwrap()
            .unwrap();
        assert!(query.model_mappings().is_none());
    }

    #[cfg(feature = "z3")]
    #[test]
    fn typed_observations_preserve_compiler_embeddings_and_quantifier_scopes() {
        use super::super::Validity;
        let definition = definition(&typed_source());
        let inject = |name: &str| format!("inj{{SortInt{{}},SortKItem{{}}}}({name}:SortInt{{}})");
        let (k, q, v, w) = (inject("K"), inject("Q"), inject("V"), inject("W"));
        let put = format!("put{{}}(M:SortMap{{}},{k},{v})");
        let read = term(&definition, &format!("get{{}}({put},{q})"));
        let old = term(&definition, &format!("get{{}}(M:SortMap{{}},{q})"));
        let apart = Predicate::Not(Arc::new(Predicate::Equals(
            term(&definition, "K:SortInt{}"),
            term(&definition, "Q:SortInt{}"),
        )));
        let known = [apart, Predicate::Ceil(old.clone())];
        assert_eq!(
            check(&definition, &known, Predicate::Equals(read, old)),
            Validity::Valid
        );
        let conditional =
            format!("choose{{SortMap{{}}}}(B:SortBool{{}},{put},put{{}}(M:SortMap{{}},{k},{w}))");
        let observed = term(
            &definition,
            &format!("project{{}}(kseq{{}}(get{{}}({conditional},{k}),dotk{{}}()))"),
        );
        let expected = term(
            &definition,
            "choose{SortInt{}}(B:SortBool{},V:SortInt{},W:SortInt{})",
        );
        assert_eq!(
            check(&definition, &[], Predicate::Ceil(observed.clone())),
            Validity::Valid
        );
        assert_eq!(
            check(&definition, &[], Predicate::Equals(observed, expected)),
            Validity::Valid
        );
        let read = term(&definition, &format!("get{{}}({put},{k})"));
        let key = crate::term::Variable::new("K", crate::term::Sort::simple("SortInt"));
        let quantified = Predicate::Forall(key, Arc::new(Predicate::Ceil(read)));
        assert_eq!(check(&definition, &[], quantified), Validity::Valid);
    }

    #[test]
    fn conditional_source_obstructions_are_checked_at_the_actual_rank() {
        let extra = r#"axiom{R} \implies{R}(\top{R}(),\equals{SortK{},R}(
            choose{SortK{}}(B:SortBool{},X:SortK{},Y:SortK{}),
            \and{SortK{}}(X:SortK{},\top{SortK{}}()))) [simplification{}()] endmodule"#;
        let original = typed_source().replace("endmodule", extra);
        let lookup = "get{}(choose{SortMap{}}(B:SortBool{},put{}(M:SortMap{},inj{SortInt{},SortKItem{}}(K:SortInt{}),inj{SortInt{},SortKItem{}}(V:SortInt{})),M:SortMap{}),inj{SortInt{},SortKItem{}}(K:SortInt{}))";
        let definition = definition(&original);
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&term(&definition, lookup))
                .unwrap()
                .is_some()
        );
        let changed = typed_source().replace("endmodule", &extra.replace("SortK{}", "SortMap{}"));
        let definition = self::definition(&changed);
        assert!(
            crate::observation::reading::Builder::new(&definition)
                .of(&term(&definition, lookup))
                .unwrap()
                .is_none()
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn finite_observation_sharing_and_cancelled_requests_are_bounded() {
        let definition = definition(source());
        let mut map = term(&definition, "M:SortMap{}");
        let int = crate::term::Sort::simple("SortInt");
        for i in 0..32 {
            map = Term::application(
                definition.symbols()["put"].clone(),
                vec![],
                vec![
                    map,
                    Term::variable(crate::term::Variable::new(format!("K{i}"), int)),
                    Term::variable(crate::term::Variable::new(format!("V{i}"), int)),
                ],
            );
        }
        let read = Term::application(
            definition.symbols()["get"].clone(),
            vec![],
            vec![map, term(&definition, "Q:SortInt{}")],
        );
        let query = crate::smt::SmtPrelude::from_definition(&definition)
            .unwrap()
            .query(
                &[],
                &Substitution::new(),
                &[Predicate::Ceil(read.clone())],
                false,
            )
            .unwrap()
            .unwrap();
        assert!(
            query.base().len() < 1_048_576,
            "{} emitted bytes",
            query.base().len()
        );
        assert!(query.model_mappings().is_none());
        let token = crate::stop::CancellationToken::new();
        token.cancel();
        let stopped = token
            .scope(|| crate::observation::reading::Builder::new(&definition).of(&read))
            .unwrap_err();
        assert_eq!(stopped.into_cause(), crate::stop::StopCause::Cancelled);
    }
}
