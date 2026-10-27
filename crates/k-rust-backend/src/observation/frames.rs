//! Deterministic known-key map witnesses. The view supplies source observations and guards;
//! it does not bind the subject map or assume that the rule matched.

use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    stop::{self, Stoppable},
    term::{Term, TermKind, VariableKind, Variables},
};

pub(crate) fn map_match(
    definition: &BackendDefinition,
    pattern: &Term,
    subject: &Term,
    pattern_variables: &Variables,
) -> Stoppable<Option<(Term, Vec<Predicate>)>> {
    let TermKind::Map {
        definition: collection,
        entries,
        rest: Some(frame),
    } = pattern.kind()
    else {
        return Ok(None);
    };
    if entries.is_empty()
        || entries.len() > 128
        || subject.sort() != pattern.sort()
        || !matches!(frame.kind(),TermKind::Variable(v) if v.kind == VariableKind::Element && pattern_variables.contains(v))
        || subject
            .attributes()
            .variables
            .iter()
            .any(|v| pattern_variables.contains(v))
    {
        return Ok(None);
    }
    let Some(ops) = definition.map_operations(&subject.sort()) else {
        return Ok(None);
    };
    if collection != &ops.collection {
        return Ok(None);
    }
    let mut purity = super::reading::Builder::new(definition);
    if !purity.pure(subject)? || !purity.pure(pattern)? {
        return Ok(None);
    }
    let mut remaining = 16_384usize;
    let mut values = Vec::with_capacity(entries.len());
    let mut rest = subject.clone();
    let mut guards = vec![Predicate::Ceil(subject.clone())];
    for (key, value_pattern) in entries {
        stop::check()?;
        // After ordinary partial substitution, any surviving original pattern variable
        // in a key would require key search. Do not turn one proposed key into coverage.
        if key
            .attributes()
            .variables
            .iter()
            .any(|v| pattern_variables.contains(v))
        {
            return Ok(None);
        }
        let (Some(raw), Some(_)) = (
            ops.lookup(definition, subject.clone(), key),
            ops.member(definition, subject.clone(), key),
        ) else {
            return Ok(None);
        };
        let Some(value) = super::pattern_observation(
            definition,
            value_pattern,
            &raw,
            pattern_variables,
            &mut remaining,
        )?
        else {
            return Ok(None);
        };
        let Some(removed) = ops.remove(definition, rest, key) else {
            return Ok(None);
        };
        rest = removed;
        guards.extend([
            Predicate::Ceil(raw.clone()),
            Predicate::Ceil(value.clone()),
            Predicate::Equals(value.clone(), raw),
        ]);
        values.push((key.clone(), value));
    }
    let witness = Term::map(collection.clone(), values, Some(rest));
    guards.extend([
        Predicate::Ceil(witness.clone()),
        Predicate::Equals(witness.clone(), subject.clone()),
    ]);
    Ok(Some((witness, guards)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        matching::{MatchMode, MatchResult, match_terms_in_definition},
        substitution::{Substitution, substitute},
        term::{Sort, Variable},
    };
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    const SOURCE: &str = r#"[] module MAIN
      hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
      hooked-sort SortBool{} [hook{}("BOOL.Bool"),hasDomainValues{}()]
      sort SortKItem{} [] sort SortK{} []
      hooked-sort SortMap{} [hook{}("MAP.Map"),unit{}(unit{}()),element{}(item{}()),concat{}(concat{}())]
      hooked-symbol unit{}() : SortMap{} [function{}(),total{}(),hook{}("MAP.unit")]
      hooked-symbol item{}(SortKItem{},SortKItem{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.element")]
      hooked-symbol concat{}(SortMap{},SortMap{}) : SortMap{} [function{}(),hook{}("MAP.concat"),assoc{}(),comm{}()]
      hooked-symbol put{}(SortMap{},SortKItem{},SortKItem{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.update")]
      hooked-symbol get{}(SortMap{},SortKItem{}) : SortKItem{} [function{}(),hook{}("MAP.lookup")]
      hooked-symbol member{}(SortKItem{},SortMap{}) : SortBool{} [function{}(),total{}(),hook{}("MAP.in_keys")]
      hooked-symbol remove{}(SortMap{},SortKItem{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.remove")]
      symbol inj{From,To}(From) : To [sortInjection{}()]
      symbol kseq{}(SortKItem{},SortK{}) : SortK{} [constructor{}()]
      symbol dotk{}() : SortK{} [constructor{}()]
      symbol project{}(SortK{}) : SortInt{} [function{}()]
      symbol f{}(SortInt{}) : SortInt{} [function{}(),total{}()]
      symbol effect{}() : SortMap{} [function{}(),impure{}()]
      axiom{R} \exists{R}(V:SortKItem{},\equals{SortKItem{},R}(V:SortKItem{},inj{SortInt{},SortKItem{}}(X:SortInt{}))) [subsort{SortInt{},SortKItem{}}()]
      axiom{R} \exists{R}(V:SortKItem{},\equals{SortKItem{},R}(V:SortKItem{},inj{SortBool{},SortKItem{}}(X:SortBool{}))) [subsort{SortBool{},SortKItem{}}()]
      axiom{R} \implies{R}(\and{R}(\top{R}(),\and{R}(\in{SortK{},R}(X:SortK{},kseq{}(inj{SortInt{},SortKItem{}}(Y:SortInt{}),dotk{}())),\top{R}())),
        \equals{SortInt{},R}(project{}(X:SortK{}),\and{SortInt{}}(Y:SortInt{},\top{SortInt{}}()))) []
      axiom{R} \implies{R}(\top{R}(),\equals{R,R}(\ceil{SortInt{},R}(project{}(X:SortK{})),
        \exists{R}(Y:SortInt{},\equals{SortK{},R}(X:SortK{},kseq{}(inj{SortInt{},SortKItem{}}(Y:SortInt{}),dotk{}()))))) []
      axiom{R} \implies{R}(\ceil{SortInt{},R}(project{}(Z:SortK{})),
        \equals{SortK{},R}(kseq{}(inj{SortInt{},SortKItem{}}(project{}(Z:SortK{})),dotk{}()),\and{SortK{}}(Z:SortK{},\top{SortK{}}()))) [simplification{}()]
    endmodule []"#;

    fn load(source: &str) -> BackendDefinition {
        BackendDefinition::internalize(&parse_definition(source).unwrap(), "MAIN").unwrap()
    }
    fn term(definition: &BackendDefinition, text: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(text).unwrap(), &[])
            .unwrap()
    }
    fn pattern(definition: &BackendDefinition, key: &str, value: &str) -> Term {
        let ops = definition.map_operations(&Sort::simple("SortMap")).unwrap();
        Term::map(
            ops.collection.clone(),
            vec![(term(definition, key), term(definition, value))],
            Some(term(definition, "R:SortMap{}")),
        )
    }
    fn fixed_pattern(definition: &BackendDefinition) -> Term {
        pattern(
            definition,
            r#"inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("0"))"#,
            "inj{SortInt{},SortKItem{}}(X:SortInt{})",
        )
    }

    #[test]
    #[ignore = "set MAP_AUDIT_KORE and MAP_AUDIT_MODULE to actual compiler output"]
    fn actual_compiler_known_key_frames_are_admitted() {
        let source = std::fs::read_to_string(std::env::var("MAP_AUDIT_KORE").unwrap()).unwrap();
        let definition = BackendDefinition::internalize(
            &parse_definition(&source).unwrap(),
            &std::env::var("MAP_AUDIT_MODULE").unwrap(),
        )
        .unwrap();
        let mut tested = 0;
        for rule in definition
            .rewrite_theory()
            .values()
            .flat_map(|g| g.values())
            .flatten()
        {
            let variables = rule.lhs.attributes().variables.clone();
            let mut pending = vec![rule.lhs.clone()];
            while let Some(pattern) = pending.pop() {
                if let TermKind::Map {
                    entries,
                    rest: Some(_),
                    ..
                } = pattern.kind()
                    && !entries.is_empty()
                {
                    let keys = entries
                        .iter()
                        .flat_map(|(k, _)| k.attributes().variables.iter())
                        .map(|v| (v.clone(), Term::int(0)))
                        .collect::<Substitution>();
                    let pattern = substitute(&pattern, &keys);
                    let subject = Term::variable(Variable::new("AuditSubject", pattern.sort()));
                    let view = map_match(&definition, &pattern, &subject, &variables).unwrap();
                    assert!(view.is_some(), "actual rule frame declined: {pattern:?}");
                    let (witness, guards) = view.unwrap();
                    #[cfg(not(feature = "z3"))]
                    let _ = &guards;
                    assert!(
                        matches!(
                            match_terms_in_definition(
                                MatchMode::Rewrite,
                                &definition,
                                &pattern,
                                &witness
                            ),
                            MatchResult::Success(_)
                        ),
                        "actual typed witness failed: {witness:?}"
                    );
                    #[cfg(feature = "z3")]
                    {
                        use crate::smt::{SmtSolver, Validity, Z3Solver};
                        let TermKind::Map { entries, .. } = pattern.kind() else {
                            unreachable!()
                        };
                        let key = &entries.iter().next().unwrap().0;
                        let raw = definition
                            .map_operations(&subject.sort())
                            .unwrap()
                            .lookup(&definition, subject.clone(), key)
                            .unwrap();
                        let typed = definition
                            .observe_stored(&raw, &Sort::simple("SortInt"))
                            .unwrap();
                        let known = [
                            Predicate::Ceil(typed.clone()),
                            Predicate::Equals(typed, Term::int(7)),
                        ];
                        let solver = Z3Solver::new(&definition).unwrap();
                        for guard in &guards {
                            assert_eq!(
                                solver
                                    .check_predicates(
                                        &known,
                                        &Substitution::new(),
                                        std::slice::from_ref(guard)
                                    )
                                    .unwrap()
                                    .unwrap(),
                                Validity::Valid,
                                "actual source guard: {guard:?}"
                            );
                        }
                    }
                    tested += 1;
                }
                pending.extend(crate::deferred::children(&pattern).into_iter().cloned());
            }
        }
        assert!(tested > 0);
    }

    #[test]
    fn witnesses_bind_only_pattern_values_and_the_deterministic_removed_frame() {
        let definition = load(SOURCE);
        let pattern = fixed_pattern(&definition);
        let subject = term(&definition, "M:SortMap{}");
        let (witness, _) = map_match(
            &definition,
            &pattern,
            &subject,
            &pattern.attributes().variables,
        )
        .unwrap()
        .unwrap();
        let MatchResult::Success(bindings) =
            match_terms_in_definition(MatchMode::Rewrite, &definition, &pattern, &witness)
        else {
            panic!("typed variable witness must match");
        };
        assert_eq!(
            bindings.get(&Variable::new("X", Sort::simple("SortInt"))),
            Some(&term(
                &definition,
                r#"project{}(kseq{}(get{}(M:SortMap{},inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("0"))),dotk{}()))"#
            ))
        );
        assert_eq!(
            bindings.get(&Variable::new("R", Sort::simple("SortMap"))),
            Some(&term(
                &definition,
                r#"remove{}(M:SortMap{},inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("0")))"#
            ))
        );
        assert!(!bindings.contains_key(&Variable::new("M", Sort::simple("SortMap"))));
        let unknown = self::pattern(
            &definition,
            "inj{SortInt{},SortKItem{}}(K:SortInt{})",
            "inj{SortInt{},SortKItem{}}(X:SortInt{})",
        );
        assert!(
            map_match(
                &definition,
                &unknown,
                &subject,
                &unknown.attributes().variables
            )
            .unwrap()
            .is_none()
        );
        let bound = substitute(
            &unknown,
            &Substitution::from([(
                Variable::new("K", Sort::simple("SortInt")),
                term(&definition, "Address:SortInt{}"),
            )]),
        );
        assert!(
            map_match(
                &definition,
                &bound,
                &subject,
                &unknown.attributes().variables
            )
            .unwrap()
            .is_some()
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn typed_domains_and_values_establish_the_entire_original_map_match_region() {
        use crate::smt::{SmtSolver, Validity, Z3Solver};
        let definition = load(SOURCE);
        let pattern = fixed_pattern(&definition);
        let subject = term(&definition, "M:SortMap{}");
        let (_, guards) = map_match(
            &definition,
            &pattern,
            &subject,
            &pattern.attributes().variables,
        )
        .unwrap()
        .unwrap();
        let typed = term(
            &definition,
            r#"project{}(kseq{}(get{}(M:SortMap{},inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("0"))),dotk{}()))"#,
        );
        let known = [
            Predicate::Ceil(typed.clone()),
            Predicate::Equals(typed, Term::int(7)),
        ];
        let solver = Z3Solver::new(&definition).unwrap();
        assert_eq!(
            solver
                .check_predicates(&known, &Substitution::new(), &guards)
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        assert_ne!(
            solver
                .check_predicates(&[], &Substitution::new(), &guards)
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
        let ops = definition.map_operations(&subject.sort()).unwrap();
        let wrong = Term::map(
            ops.collection.clone(),
            vec![(
                term(
                    &definition,
                    r#"inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("0"))"#,
                ),
                term(
                    &definition,
                    r#"inj{SortBool{},SortKItem{}}(\dv{SortBool{}}("true"))"#,
                ),
            )],
            None,
        );
        let (_, wrong_guards) = map_match(
            &definition,
            &pattern,
            &wrong,
            &pattern.attributes().variables,
        )
        .unwrap()
        .unwrap();
        assert_ne!(
            solver
                .check_predicates(&[], &Substitution::new(), &wrong_guards)
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
    }

    #[cfg(feature = "z3")]
    #[test]
    fn recovered_symbolic_keys_and_determined_values_do_not_bind_subject_variables() {
        use crate::{
            rewrite::{RecoveredMatch, recover_indeterminate_match},
            simplify::SimplificationOptions,
            smt::{SmtSolver, Validity, Z3Solver},
        };
        let definition = load(SOURCE);
        let original = pattern(
            &definition,
            "inj{SortInt{},SortKItem{}}(K:SortInt{})",
            "inj{SortInt{},SortKItem{}}(X:SortInt{})",
        );
        let subject = term(&definition, "M:SortMap{}");
        let key = Variable::new("K", Sort::simple("SortInt"));
        let value = Variable::new("X", Sort::simple("SortInt"));
        let solver = Z3Solver::new(&definition).unwrap();
        let typed = term(
            &definition,
            "project{}(kseq{}(get{}(M:SortMap{},inj{SortInt{},SortKItem{}}(Address:SortInt{})),dotk{}()))",
        );
        let known = [
            Predicate::Ceil(typed.clone()),
            Predicate::Equals(typed, Term::int(7)),
        ];
        for determined in [false, true] {
            let mut bindings =
                Substitution::from([(key.clone(), term(&definition, "Address:SortInt{}"))]);
            let mut known = known.to_vec();
            if determined {
                bindings.insert(value.clone(), term(&definition, "Expected:SortInt{}"));
                known.push(Predicate::Equals(
                    term(&definition, "Expected:SortInt{}"),
                    Term::int(9),
                ));
            }
            let recovered = recover_indeterminate_match(
                &definition,
                &original.attributes().variables,
                bindings,
                vec![(original.clone(), subject.clone())],
                &known,
                SimplificationOptions::default(),
                &solver,
            )
            .unwrap()
            .unwrap();
            let RecoveredMatch::Matched {
                solution,
                remainder,
            } = recovered
            else {
                panic!("source observation must recover")
            };
            assert!(remainder.is_empty(), "{remainder:?}");
            assert!(
                solution
                    .substitution()
                    .keys()
                    .all(|v| original.attributes().variables.contains(v)),
                "subject bindings escaped: {:?}",
                solution.substitution()
            );
            assert_eq!(
                solver
                    .check_predicates(&known, &Substitution::new(), solution.conditions())
                    .unwrap()
                    .unwrap()
                    == Validity::Valid,
                !determined,
                "a supplied value's equality is still an obligation"
            );
        }
    }

    #[cfg(feature = "z3")]
    #[test]
    fn source_hook_aliases_share_observations_at_their_actual_compatible_ranks() {
        use crate::smt::{SmtSolver, Validity, Z3Solver};
        let source = SOURCE.replace("endmodule",r#"
          hooked-symbol aGet{}(SortMap{},SortInt{}) : SortKItem{} [function{}(),hook{}("MAP.lookup")]
          hooked-symbol aMember{}(SortInt{},SortMap{}) : SortBool{} [function{}(),total{}(),hook{}("MAP.in_keys")]
        endmodule"#);
        let definition = load(&source);
        let pattern = fixed_pattern(&definition);
        let subject = term(&definition, "M:SortMap{}");
        let (_, guards) = map_match(
            &definition,
            &pattern,
            &subject,
            &pattern.attributes().variables,
        )
        .unwrap()
        .unwrap();
        let typed = term(
            &definition,
            r#"project{}(kseq{}(get{}(M:SortMap{},inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("0"))),dotk{}()))"#,
        );
        assert_eq!(
            Z3Solver::new(&definition)
                .unwrap()
                .check_predicates(
                    &[
                        Predicate::Ceil(typed.clone()),
                        Predicate::Equals(typed, Term::int(7))
                    ],
                    &Substitution::new(),
                    &guards
                )
                .unwrap()
                .unwrap(),
            Validity::Valid
        );
    }

    #[test]
    fn source_obstructions_effects_and_unbound_function_inverses_decline() {
        let definition = load(SOURCE);
        let pattern = fixed_pattern(&definition);
        assert!(
            map_match(
                &definition,
                &pattern,
                &term(&definition, "effect{}()"),
                &pattern.attributes().variables
            )
            .unwrap()
            .is_none()
        );
        let function_pattern = self::pattern(
            &definition,
            r#"inj{SortInt{},SortKItem{}}(\dv{SortInt{}}("0"))"#,
            "inj{SortInt{},SortKItem{}}(f{}(X:SortInt{}))",
        );
        assert!(
            map_match(
                &definition,
                &function_pattern,
                &term(&definition, "M:SortMap{}"),
                &function_pattern.attributes().variables
            )
            .unwrap()
            .is_none()
        );
        let changed = load(&SOURCE.replace(
            "get{}(SortMap{},SortKItem{}) : SortKItem{} [function{}(),hook",
            "get{}(SortMap{},SortKItem{}) : SortKItem{} [function{}(),impure{}(),hook",
        ));
        let pattern = fixed_pattern(&changed);
        assert!(
            map_match(
                &changed,
                &pattern,
                &term(&changed, "M:SortMap{}"),
                &pattern.attributes().variables
            )
            .unwrap()
            .is_none()
        );
        let token = crate::stop::CancellationToken::new();
        token.cancel();
        let stopped = token
            .scope(|| {
                map_match(
                    &definition,
                    &fixed_pattern(&definition),
                    &term(&definition, "M:SortMap{}"),
                    &fixed_pattern(&definition).attributes().variables,
                )
            })
            .unwrap_err();
        assert_eq!(stopped.into_cause(), crate::stop::StopCause::Cancelled);
    }
}
