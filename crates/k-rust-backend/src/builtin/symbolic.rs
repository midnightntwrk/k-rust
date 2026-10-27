//! Selected decreasing identities of pure functional symbolic hook operands.
//! Called only after concrete evaluation declines. The caller must retain the original
//! strict arguments' definedness through `Simplification::hook`.

use k_rust_kore::names::BuiltinSort;

use super::{BuiltinResult, CollectionOperand, read_collection_item, read_small_int, stored_at};
use crate::{
    deferred::pure_functional_term,
    definition::BackendDefinition,
    rule::Predicate,
    term::{CollectionMetadata, DomainKind, Sort, Term, TermKind},
};

/// ```toml algorithm-site
/// id = "backend.simplify.term"
/// role = "part"
/// sites = ["reduce", "scalar", "map", "key_fact"]
/// ```
pub(crate) fn reduce(
    definition: &BackendDefinition,
    term: &Term,
    known: &[Predicate],
) -> BuiltinResult {
    scalar(definition, term)
        .or_else(|| map(definition, term, known))
        .into()
}

fn scalar(definition: &BackendDefinition, term: &Term) -> Option<Term> {
    let TermKind::Application {
        symbol, arguments, ..
    } = term.kind()
    else {
        return None;
    };
    let hook = symbol.attributes.hook.as_deref()?;
    if !matches!(
        hook,
        "INT.and" | "INT.or" | "INT.xor" | "INT.shl" | "INT.shr"
    ) {
        return None;
    }
    let [left, right] = arguments.as_slice() else {
        return None;
    };
    let int = Sort::builtin(BuiltinSort::Int);
    if term.sort() != int
        || left.sort() != int
        || right.sort() != int
        || definition.domain_kind(&int) != Some(DomainKind::Int)
    {
        return None;
    }
    let left_zero = read_small_int(left) == Some(0);
    let right_zero = read_small_int(right) == Some(0);
    let result = match hook {
        "INT.and" if left_zero || right_zero => Term::int(0),
        "INT.and" | "INT.or" if left == right => left.clone(),
        "INT.xor" if left == right => Term::int(0),
        "INT.or" | "INT.xor" if left_zero => right.clone(),
        "INT.or" | "INT.xor" | "INT.shl" | "INT.shr" if right_zero => left.clone(),
        _ => return None,
    };
    pure_functional_term(definition, term).then_some(result)
}

/// A map write is overwrite, never disjoint concatenation with an opaque frame.
fn map(definition: &BackendDefinition, term: &Term, known: &[Predicate]) -> Option<Term> {
    let TermKind::Application {
        symbol,
        sort_arguments,
        arguments,
    } = term.kind()
    else {
        return None;
    };
    let hook = symbol.attributes.hook.as_deref()?;
    let outer_key = match (hook, arguments.as_slice()) {
        ("MAP.lookup", [_, key]) | ("MAP.update", [_, key, _]) => key,
        _ => return None,
    };
    let TermKind::Application {
        symbol: write,
        arguments: written,
        ..
    } = arguments[0].kind()
    else {
        return None;
    };
    if write.attributes.hook.as_deref() != Some("MAP.update") {
        return None;
    }
    let [base, key, value] = written.as_slice() else {
        return None;
    };
    let Some(CollectionMetadata::Map(collection)) = write.attributes.result_collection.as_ref()
    else {
        return None;
    };
    let map_sort = arguments[0].sort();
    if base.sort() != map_sort || map_sort != Sort::simple(collection.map_sort.clone()) {
        return None;
    }
    let sorts = Some(definition.sort_graph());
    let key = stored_at(sorts, key, &collection.key_sort)?;
    let value = stored_at(sorts, value, &collection.value_sort)?;
    let outer_key = match read_collection_item(sorts, outer_key, &collection.key_sort) {
        CollectionOperand::Element(key) => key.into_owned(),
        CollectionOperand::Wider { .. } | CollectionOperand::Unrelated => return None,
    };
    let equal = key == outer_key || key_fact(definition, known, &key, &outer_key, true);
    let result = if hook == "MAP.lookup" {
        if equal {
            stored_at(sorts, &value, &term.sort())?
        } else if super::values_differ(sorts, &key, &outer_key)
            || key_fact(definition, known, &key, &outer_key, false)
        {
            Term::application(
                symbol.clone(),
                *sort_arguments,
                vec![base.clone(), arguments[1].clone()],
            )
        } else {
            return None;
        }
    } else {
        if !equal
            || term.sort() != map_sort
            || symbol.attributes.result_collection != write.attributes.result_collection
        {
            return None;
        }
        // The outer declaration is retained verbatim; replacing the first argument must
        // preserve its rank, and its new key/value must fit the collection's stored sorts.
        stored_at(sorts, &arguments[1], &collection.key_sort)?;
        stored_at(sorts, &arguments[2], &collection.value_sort)?;
        Term::application(
            symbol.clone(),
            *sort_arguments,
            vec![base.clone(), arguments[1].clone(), arguments[2].clone()],
        )
    };
    pure_functional_term(definition, term).then_some(result)
}

/// Read only explicit scoped equations/disequations; unknown aliases cause no solver query.
/// Facts over injected keys are compared at the collection's key sort using the same reader.
fn key_fact(
    definition: &BackendDefinition,
    known: &[Predicate],
    left: &Term,
    right: &Term,
    equal: bool,
) -> bool {
    known.iter().any(|fact| {
        let fact = match (equal, fact) {
            (false, Predicate::Not(inner)) => inner.as_ref(),
            (true, Predicate::Equals(..)) => fact,
            _ => return false,
        };
        let Predicate::Equals(a, b) = fact else {
            return false;
        };
        let read =
            |term| match read_collection_item(Some(definition.sort_graph()), term, &left.sort()) {
                CollectionOperand::Element(term) => Some(term.into_owned()),
                CollectionOperand::Wider { .. } | CollectionOperand::Unrelated => None,
            };
        let (Some(a), Some(b)) = (read(a), read(b)) else {
            return false;
        };
        (&a == left && &b == right) || (&a == right && &b == left)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        rule::Predicate,
        simplify::{SimplificationOptions, simplify},
    };
    use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

    fn definition() -> BackendDefinition {
        let mut source = String::from(
            r#"[] module MAIN
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            symbol partial{}(SortInt{}) : SortInt{} [function{}()]
            symbol pair{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}()]
            symbol effect{}(SortInt{}) : SortInt{} [function{}(), total{}(), impure{}()]
            hooked-sort SortMap{} [hook{}("MAP.Map"), unit{}(unit{}()), element{}(item{}()), concat{}(concat{}())]
            hooked-symbol unit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
            hooked-symbol item{}(SortInt{}, SortInt{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
            hooked-symbol concat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
            hooked-symbol put{}(SortMap{}, SortInt{}, SortInt{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.update")]
            hooked-symbol get{}(SortMap{}, SortInt{}) : SortInt{} [function{}(), hook{}("MAP.lookup")]
        "#,
        );
        for (name, hook) in [
            ("band", "and"),
            ("bor", "or"),
            ("bxor", "xor"),
            ("shl", "shl"),
            ("shr", "shr"),
        ] {
            source.push_str(&format!(r#"hooked-symbol {name}{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}(), hook{{}}("INT.{hook}")]"#));
        }
        source.push_str(" endmodule []");
        BackendDefinition::internalize(&parse_definition(&source).unwrap(), "MAIN").unwrap()
    }

    fn term(definition: &BackendDefinition, source: &str) -> Term {
        definition
            .internalize_term(&parse_pattern(source).unwrap(), &[])
            .unwrap()
    }

    #[test]
    fn scalar_laws_preserve_partial_operand_obligations_without_source_steps() {
        let definition = definition();
        let x = "partial{}(X:SortInt{})";
        let zero = r#"\dv{SortInt{}}("0")"#;
        for (name, left, right, expected) in [
            ("band", x, x, x),
            ("bor", x, x, x),
            ("bxor", x, x, zero),
            ("band", x, zero, zero),
            ("band", zero, x, zero),
            ("bor", x, zero, x),
            ("bor", zero, x, x),
            ("bxor", x, zero, x),
            ("bxor", zero, x, x),
            ("shl", x, zero, x),
            ("shr", x, zero, x),
        ] {
            let input = term(&definition, &format!("{name}{{}}({left}, {right})"));
            let result = simplify(&definition, &input, SimplificationOptions::default())
                .unwrap()
                .unwrap();
            assert_eq!(result.term, term(&definition, expected), "{name}");
            assert!(
                result
                    .constraints()
                    .contains(&Predicate::Ceil(term(&definition, x))),
                "{name}: {:?}",
                result.constraints()
            );
            assert!(
                result
                    .applied_rules
                    .iter()
                    .all(|rule| rule.starts_with("builtin:"))
            );
            assert!(result.effects.is_empty());
        }
    }

    #[test]
    fn scalar_laws_decline_nonfunctional_effectful_and_unselected_shapes() {
        let definition = definition();
        for source in [
            "bxor{}(@X:SortInt{}, @X:SortInt{})",
            "bxor{}(effect{}(X:SortInt{}), effect{}(X:SortInt{}))",
            "bxor{}(X:SortInt{}, Y:SortInt{})",
            r#"shl{}(\dv{SortInt{}}("0"), X:SortInt{})"#,
            r#"shr{}(X:SortInt{}, \dv{SortInt{}}("-1"))"#,
        ] {
            assert_eq!(
                reduce(&definition, &term(&definition, source), &[]),
                BuiltinResult::NotApplicable,
                "{source}"
            );
        }
    }

    #[test]
    fn scalar_laws_require_the_declared_int_domain() {
        let syntax = parse_definition(
            r#"[] module MAIN
            sort SortInt{} []
            hooked-symbol bxor{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.xor")]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        assert_eq!(
            reduce(
                &definition,
                &term(&definition, "bxor{}(X:SortInt{}, X:SortInt{})"),
                &[]
            ),
            BuiltinResult::NotApplicable
        );
    }

    #[test]
    fn admission_visits_shared_dags_without_expanding_the_tree() {
        let definition = definition();
        let mut x = term(&definition, "X:SortInt{}");
        let pair = definition.symbols()["pair"].clone();
        for _ in 0..64 {
            x = Term::application(pair.clone(), vec![], vec![x.clone(), x]);
        }
        let input = Term::application(
            definition.symbols()["bxor"].clone(),
            vec![],
            vec![x.clone(), x],
        );
        assert_eq!(
            reduce(&definition, &input, &[]),
            BuiltinResult::Value(Term::int(0))
        );
    }

    #[test]
    fn concrete_negative_values_and_undefined_shifts_keep_existing_results() {
        let definition = definition();
        for (source, expected) in [
            (
                r#"bxor{}(\dv{SortInt{}}("-37"), \dv{SortInt{}}("-37"))"#,
                Some(0),
            ),
            (
                r#"shr{}(\dv{SortInt{}}("-37"), \dv{SortInt{}}("0"))"#,
                Some(-37),
            ),
            (r#"shl{}(\dv{SortInt{}}("0"), \dv{SortInt{}}("-1"))"#, None),
        ] {
            let result = simplify(
                &definition,
                &term(&definition, source),
                SimplificationOptions::default(),
            )
            .unwrap()
            .unwrap();
            match expected {
                Some(value) => assert_eq!(result.term, Term::int(value)),
                None => assert!(result.constraints().contains(&Predicate::False)),
            }
        }
    }
    #[test]
    fn map_read_write_and_overwrite_preserve_strictness_and_the_symbolic_frame() {
        let definition = definition();
        let value = "partial{}(V:SortInt{})";
        for (source, expected) in [
            (
                format!("get{{}}(put{{}}(M:SortMap{{}}, K:SortInt{{}}, {value}), K:SortInt{{}})"),
                value.to_owned(),
            ),
            (
                format!(
                    "put{{}}(put{{}}(M:SortMap{{}}, K:SortInt{{}}, {value}), K:SortInt{{}}, W:SortInt{{}})"
                ),
                "put{}(M:SortMap{}, K:SortInt{}, W:SortInt{})".to_owned(),
            ),
        ] {
            let result = simplify(
                &definition,
                &term(&definition, &source),
                SimplificationOptions::default(),
            )
            .unwrap()
            .unwrap();
            assert_eq!(result.term, term(&definition, &expected));
            assert!(
                result
                    .constraints()
                    .contains(&Predicate::Ceil(term(&definition, value)))
            );
            assert!(
                !result
                    .constraints()
                    .iter()
                    .any(|p| matches!(p, Predicate::Absent(_)))
            );
        }
    }

    #[test]
    fn map_aliases_need_evidence_and_scoped_evidence_does_not_leak() {
        let definition = definition();
        let source = term(
            &definition,
            "get{}(put{}(M:SortMap{}, K:SortInt{}, V:SortInt{}), J:SortInt{})",
        );
        assert_eq!(
            reduce(&definition, &source, &[]),
            BuiltinResult::NotApplicable
        );
        let k = term(&definition, "K:SortInt{}");
        let j = term(&definition, "J:SortInt{}");
        let unequal = Predicate::Not(std::sync::Arc::new(Predicate::Equals(j.clone(), k.clone())));
        assert_eq!(
            reduce(&definition, &source, &[unequal]),
            BuiltinResult::Value(term(&definition, "get{}(M:SortMap{}, J:SortInt{})"))
        );
        assert_eq!(
            reduce(&definition, &source, &[Predicate::Equals(k, j)]),
            BuiltinResult::Value(term(&definition, "V:SortInt{}"))
        );
        assert_eq!(
            reduce(&definition, &source, &[]),
            BuiltinResult::NotApplicable
        );
        let noninjective = term(
            &definition,
            "get{}(put{}(M:SortMap{}, partial{}(K:SortInt{}), V:SortInt{}), partial{}(J:SortInt{}))",
        );
        assert_eq!(
            reduce(&definition, &noninjective, &[]),
            BuiltinResult::NotApplicable
        );
    }

    #[test]
    fn map_distinct_read_keeps_the_discarded_value_obligation() {
        let definition = definition();
        let source = term(
            &definition,
            r#"get{}(put{}(M:SortMap{}, \dv{SortInt{}}("1"), partial{}(V:SortInt{})), \dv{SortInt{}}("2"))"#,
        );
        let result = simplify(&definition, &source, SimplificationOptions::default())
            .unwrap()
            .unwrap();
        assert_eq!(
            result.term,
            term(&definition, r#"get{}(M:SortMap{}, \dv{SortInt{}}("2"))"#)
        );
        assert!(result.constraints().contains(&Predicate::Ceil(term(
            &definition,
            "partial{}(V:SortInt{})"
        ))));
    }

    #[test]
    fn map_laws_decline_set_valued_and_effectful_operands() {
        let definition = definition();
        for source in [
            "get{}(put{}(@M:SortMap{}, K:SortInt{}, V:SortInt{}), K:SortInt{})",
            "get{}(put{}(M:SortMap{}, K:SortInt{}, effect{}(V:SortInt{})), K:SortInt{})",
            "put{}(put{}(M:SortMap{}, K:SortInt{}, effect{}(V:SortInt{})), K:SortInt{}, W:SortInt{})",
        ] {
            assert_eq!(
                reduce(&definition, &term(&definition, source), &[]),
                BuiltinResult::NotApplicable,
                "{source}"
            );
        }
    }
    #[test]
    fn typed_map_laws_keep_key_and_result_injections() {
        let syntax = parse_definition(r#"[] module MAIN
            sort SortKey{} []
            sort SortSmallKey{} []
            sort SortValue{} []
            sort SortSmallValue{} []
            sort SortItem{} []
            symbol inj{From, To}(From) : To [sortInjection{}()]
            axiom{R} \exists{R}(V:SortKey{}, \equals{SortKey{}, R}(V:SortKey{}, inj{SortSmallKey{}, SortKey{}}(X:SortSmallKey{}))) [subsort{SortSmallKey{}, SortKey{}}()]
            axiom{R} \exists{R}(V:SortValue{}, \equals{SortValue{}, R}(V:SortValue{}, inj{SortSmallValue{}, SortValue{}}(X:SortSmallValue{}))) [subsort{SortSmallValue{}, SortValue{}}()]
            axiom{R} \exists{R}(V:SortItem{}, \equals{SortItem{}, R}(V:SortItem{}, inj{SortValue{}, SortItem{}}(X:SortValue{}))) [subsort{SortValue{}, SortItem{}}()]
            hooked-sort SortMap{} [hook{}("MAP.Map"), unit{}(unit{}()), element{}(item{}()), concat{}(concat{}())]
            hooked-symbol unit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
            hooked-symbol item{}(SortKey{}, SortValue{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
            hooked-symbol concat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
            hooked-symbol put{}(SortMap{}, SortSmallKey{}, SortSmallValue{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.update")]
            hooked-symbol get{}(SortMap{}, SortKey{}) : SortItem{} [function{}(), hook{}("MAP.lookup")]
            endmodule []"#).unwrap();
        let definition = BackendDefinition::internalize(&syntax, "MAIN").unwrap();
        let source = term(
            &definition,
            "get{}(put{}(M:SortMap{}, K:SortSmallKey{}, V:SortSmallValue{}), inj{SortSmallKey{}, SortKey{}}(K:SortSmallKey{}))",
        );
        let expected = term(
            &definition,
            "inj{SortSmallValue{}, SortItem{}}(V:SortSmallValue{})",
        );
        assert_eq!(
            reduce(&definition, &source, &[]),
            BuiltinResult::Value(expected)
        );

        let TermKind::Application {
            symbol, arguments, ..
        } = source.kind()
        else {
            panic!()
        };
        let mut wrong_result = symbol.as_ref().clone();
        wrong_result.result_sort = Sort::simple("SortSmallKey");
        let wrong_result =
            Term::application(std::sync::Arc::new(wrong_result), vec![], arguments.clone());
        assert_eq!(
            reduce(&definition, &wrong_result, &[]),
            BuiltinResult::NotApplicable
        );
        let wrong_write = Term::application(
            definition.symbols()["put"].clone(),
            vec![],
            vec![
                term(&definition, "M:SortMap{}"),
                term(&definition, "K:SortSmallKey{}"),
                term(&definition, "W:SortKey{}"),
            ],
        );
        let wrong_value = Term::application(
            symbol.clone(),
            vec![],
            vec![wrong_write, arguments[1].clone()],
        );
        assert_eq!(
            reduce(&definition, &wrong_value, &[]),
            BuiltinResult::NotApplicable
        );
    }

    #[test]
    fn scoped_map_disequality_works_through_the_simplifier() {
        let definition = definition();
        let source = term(
            &definition,
            "get{}(put{}(M:SortMap{}, K:SortInt{}, partial{}(V:SortInt{})), J:SortInt{})",
        );
        let unequal = Predicate::Not(std::sync::Arc::new(Predicate::Equals(
            term(&definition, "K:SortInt{}"),
            term(&definition, "J:SortInt{}"),
        )));
        let result = crate::simplify::simplify_with_solver(
            &definition,
            &source,
            &[unequal],
            SimplificationOptions::default(),
            &crate::smt::NoSolver,
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            result.term,
            term(&definition, "get{}(M:SortMap{}, J:SortInt{})")
        );
        assert!(result.constraints().contains(&Predicate::Ceil(term(
            &definition,
            "partial{}(V:SortInt{})"
        ))));
        let plain = simplify(&definition, &source, SimplificationOptions::default())
            .unwrap()
            .unwrap();
        assert_eq!(plain.term, source);
    }
    #[test]
    fn distinct_write_chains_normalize_with_explicit_budgets() {
        let definition = definition();
        for n in [16, 64, 128] {
            let base = term(&definition, "M:SortMap{}");
            let mut writes = base.clone();
            for key in 1..=n {
                writes = Term::application(
                    definition.symbols()["put"].clone(),
                    vec![],
                    vec![writes, Term::int(key), Term::int(key)],
                );
            }
            let source = Term::application(
                definition.symbols()["get"].clone(),
                vec![],
                vec![writes, Term::int(0)],
            );
            let before = k_rust_kore::measure::snapshot();
            let started = std::time::Instant::now();
            let result = simplify(
                &definition,
                &source,
                SimplificationOptions::keep_partial(512),
            )
            .unwrap()
            .unwrap();
            let elapsed = started.elapsed();
            let after = k_rust_kore::measure::snapshot();
            assert_eq!(
                result.term,
                Term::application(
                    definition.symbols()["get"].clone(),
                    vec![],
                    vec![base, Term::int(0)]
                )
            );
            assert!(result.exhausted.is_none());
            let evaluations = after.get(k_rust_kore::measure::Counter::SimplifyBuiltinEvaluations)
                - before.get(k_rust_kore::measure::Counter::SimplifyBuiltinEvaluations);
            assert_eq!(evaluations, n as u64);
            eprintln!(
                "distinct write chain n={n}: {evaluations} hook reductions, {} us",
                elapsed.as_micros()
            );
            let bounded = simplify(&definition, &source, SimplificationOptions::keep_partial(2))
                .unwrap()
                .unwrap();
            assert!(bounded.exhausted.is_some());
        }
    }
    #[test]
    fn admission_respects_transitive_and_unindexed_effects_and_residual_binders() {
        for unindexed in [false, true] {
            let lhs = if unindexed {
                "X:SortInt{}"
            } else {
                "indirect{}(X:SortInt{})"
            };
            let source = format!(
                r#"[] module MAIN
                hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
                symbol effect{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}(), impure{{}}()]
                symbol indirect{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
                hooked-symbol bxor{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}(), hook{{}}("INT.xor")]
                axiom{{R}} \implies{{R}}(\top{{R}}(),
                    \equals{{SortInt{{}}, R}}({lhs}, \and{{SortInt{{}}}}(effect{{}}(X:SortInt{{}}), \top{{SortInt{{}}}}())))
                    [simplification{{}}()]
                endmodule []"#
            );
            let definition =
                BackendDefinition::internalize(&parse_definition(&source).unwrap(), "MAIN")
                    .unwrap();
            let operand = if unindexed {
                "X:SortInt{}"
            } else {
                "indirect{}(X:SortInt{})"
            };
            assert_eq!(
                reduce(
                    &definition,
                    &term(&definition, &format!("bxor{{}}({operand}, {operand})")),
                    &[]
                ),
                BuiltinResult::NotApplicable
            );
        }
        let definition = definition();
        for binder in [false, true] {
            let mut symbol = definition.symbols()["partial"].as_ref().clone();
            symbol.attributes.binder = binder;
            symbol.attributes.macro_or_alias = !binder;
            let operand = Term::application(
                std::sync::Arc::new(symbol),
                vec![],
                vec![term(&definition, "X:SortInt{}")],
            );
            let source = Term::application(
                definition.symbols()["bxor"].clone(),
                vec![],
                vec![operand.clone(), operand],
            );
            assert_eq!(
                reduce(&definition, &source, &[]),
                BuiltinResult::NotApplicable
            );
        }
    }
}
