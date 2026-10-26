//! Admission controls use actual internalized equations, attributes, matching and domain rules.

use super::*;
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};
use k_rust_kore::kore::{ast::Pattern, printer::Printer};

fn source(extra: &str) -> String {
    format!(
        r#"[]
module MAIN
  hooked-sort SortInt{{}} [hook{{}}("INT.Int"), hasDomainValues{{}}()]
  hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
  sort SortOp{{}} []
  symbol a{{}}() : SortOp{{}} [constructor{{}}(), functional{{}}()]
  symbol b{{}}() : SortOp{{}} [constructor{{}}(), functional{{}}()]
  symbol wrap{{}}(SortOp{{}}) : SortOp{{}} [constructor{{}}(), functional{{}}()]
  hooked-symbol plus{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
    [function{{}}(), total{{}}(), hook{{}}("INT.add"), smt-hook{{}}("+")]
  hooked-symbol lt{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
    [function{{}}(), total{{}}(), hook{{}}("INT.lt"), smt-hook{{}}("<")]
  hooked-symbol ge{{}}(SortInt{{}}, SortInt{{}}) : SortBool{{}}
    [function{{}}(), total{{}}(), hook{{}}("INT.ge"), smt-hook{{}}(">=")]
  hooked-symbol not{{}}(SortBool{{}}) : SortBool{{}}
    [function{{}}(), total{{}}(), hook{{}}("BOOL.not"), smt-hook{{}}("not")]
  hooked-symbol ediv{{}}(SortInt{{}}, SortInt{{}}) : SortInt{{}}
    [function{{}}(), hook{{}}("INT.ediv"), smt-hook{{}}("div")]
  symbol bit{{}}(SortBool{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
  symbol twoBits{{}}(SortBool{{}}, SortBool{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
  symbol magnitude{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
  symbol dispatch{{}}(SortOp{{}}, SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
  symbol outer{{}}(SortInt{{}}) : SortInt{{}} [function{{}}(), total{{}}()]
  symbol effect{{}}() : SortInt{{}} [function{{}}(), total{{}}(), impure{{}}()]
  {extra}
endmodule []"#
    )
}

fn definition(extra: &str) -> BackendDefinition {
    BackendDefinition::internalize(&parse_definition(&source(extra)).unwrap(), "MAIN").unwrap()
}

#[test]
fn unhooked_builtin_names_keep_their_carriers_and_renamed_sorts_stay_outside_scalar_admission() {
    for (sort, hook) in [("SortBool", "BOOL.Bool"), ("SortInt", "INT.Int")] {
        let text = source(&bit_rows()).replace(
            &format!("hooked-sort {sort}{{}} [hook{{}}(\"{hook}\"), hasDomainValues{{}}()]"),
            &format!("sort {sort}{{}} [hasDomainValues{{}}()]"),
        );
        let d = BackendDefinition::internalize(&parse_definition(&text).unwrap(), "MAIN").unwrap();
        assert!(
            Catalog::new(&d)
                .admit(&term(&d, "bit{}(B:SortBool{})"))
                .unwrap()
                .is_ok()
        );
    }
    for (old, new, call) in [
        ("SortBool", "SortUserBool", "bit{}(B:SortUserBool{})"),
        ("SortInt", "SortUserInt", "bit{}(B:SortBool{})"),
    ] {
        let text = source(&bit_rows()).replace(old, new);
        let d = BackendDefinition::internalize(&parse_definition(&text).unwrap(), "MAIN").unwrap();
        assert_eq!(
            Catalog::new(&d).admit(&term(&d, call)).unwrap(),
            Err(Rejected::Unsupported)
        );
    }
}

fn term(d: &BackendDefinition, text: &str) -> Term {
    d.internalize_term(&parse_pattern(text).unwrap(), &[])
        .unwrap()
}

fn int(n: i64) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{n}")"#)
}
fn boolv(b: bool) -> String {
    format!(r#"\dv{{SortBool{{}}}}("{b}")"#)
}

fn equation(lhs: &str, rhs: &str, guard: Option<&str>, attrs: &str) -> String {
    let mut condition = guard.map_or_else(
        || "\\top{R}()".to_owned(),
        |g| format!("\\equals{{SortBool{{}},R}}({g},{})", boolv(true)),
    );
    let mut lhs = lhs.to_owned();
    if !attrs.contains("simplification")
        && let Pattern::Application { symbol, arguments } = &parse_pattern(&lhs).unwrap()
    {
        let sorts = match symbol.name.as_str() {
            "bit" => vec!["SortBool"],
            "twoBits" => vec!["SortBool", "SortBool"],
            "dispatch" => vec!["SortOp", "SortInt"],
            "magnitude" | "outer" => vec!["SortInt"],
            other => panic!("fixture signature for {other}"),
        };
        let mut binders = "\\top{R}()".to_owned();
        let mut formals = Vec::new();
        for (i, (argument, sort)) in arguments.iter().zip(sorts).enumerate().rev() {
            let formal = format!("KRSInput{i}:{sort}{{}}");
            let argument = Printer::compact().print_pattern(argument);
            binders = format!("\\and{{R}}(\\in{{{sort}{{}},R}}({formal},{argument}),{binders})");
            formals.push(formal);
        }
        formals.reverse();
        lhs = format!("{}{{}}({})", symbol.name, formals.join(","));
        condition = format!("\\and{{R}}({condition},{binders})");
    }
    format!(
        "axiom{{R}} \\implies{{R}}({condition}, \\equals{{SortInt{{}},R}}({lhs}, \\and{{SortInt{{}}}}({rhs},\\top{{SortInt{{}}}}()))) [{attrs}]"
    )
}

fn evaluate(d: &BackendDefinition, summary: &Summary, inputs: Vec<Term>) -> Term {
    let bindings = summary.parameters.iter().cloned().zip(inputs).collect();
    let value = |t: &Term| {
        crate::simplify::simplify(
            d,
            &substitute(t, &bindings),
            SimplificationOptions::default(),
        )
        .unwrap()
        .unwrap()
        .term
    };
    let mut decision = summary.body.as_ref();
    loop {
        match decision {
            Decision::Value(t) => return value(t),
            Decision::If { test, yes, no } => {
                let holds = match test {
                    Atom::Bool(t) => boolean(&value(t)).unwrap(),
                    Atom::Less(a, b) => {
                        crate::builtin::read_int(&value(a)).unwrap()
                            < crate::builtin::read_int(&value(b)).unwrap()
                    }
                    Atom::Equal(a, b) => value(a) == value(b),
                };
                decision = if holds { yes.as_ref() } else { no.as_ref() };
            }
        }
    }
}

fn bit_rows() -> String {
    [
        equation(&format!("bit{{}}({})", boolv(true)), &int(1), None, ""),
        equation(&format!("bit{{}}({})", boolv(false)), &int(0), None, ""),
    ]
    .join("\n")
}

#[test]
fn boolean_rows_and_complementary_comparisons_derive_finite_decisions() {
    let zero = int(0);
    let lt = format!("lt{{}}(X:SortInt{{}},{zero})");
    let ge = format!("ge{{}}(X:SortInt{{}},{zero})");
    let d = definition(
        &[
            bit_rows(),
            equation("magnitude{}(X:SortInt{})", &int(7), Some(&lt), ""),
            equation("magnitude{}(X:SortInt{})", &int(9), Some(&ge), ""),
            equation("outer{}(X:SortInt{})", &format!("bit{{}}({lt})"), None, ""),
        ]
        .join("\n"),
    );
    let mut catalog = Catalog::new(&d);
    let bit = catalog
        .admit(&term(&d, "bit{}(P:SortBool{})"))
        .unwrap()
        .unwrap();
    assert_eq!(bit.parameters.len(), 1);
    assert_eq!(bit.source_rules.len(), 2);
    assert_eq!(
        bit.source_rules
            .iter()
            .map(|r| r.attributes.origins.len())
            .sum::<usize>(),
        2
    );
    assert!(matches!(
        bit.body.as_ref(),
        Decision::If {
            test: Atom::Bool(_),
            ..
        }
    ));
    let magnitude = catalog
        .admit(&term(&d, "magnitude{}(X:SortInt{})"))
        .unwrap()
        .unwrap();
    assert!(matches!(
        magnitude.body.as_ref(),
        Decision::If {
            test: Atom::Less(..),
            ..
        }
    ));
    let outer = catalog
        .admit(&term(&d, "outer{}(X:SortInt{})"))
        .unwrap()
        .unwrap();
    assert_eq!(outer.dependencies, BTreeSet::from([bit.key.clone()]));
    assert_eq!(catalog.accepted.len(), 3);
    for b in [false, true] {
        assert_eq!(
            crate::builtin::read_int(&evaluate(&d, &bit, vec![term(&d, &boolv(b))])).unwrap(),
            i64::from(b).into()
        );
    }
    for (x, expected) in [(-7, 7), (0, 9), (11, 9)] {
        assert_eq!(
            crate::builtin::read_int(&evaluate(&d, &magnitude, vec![term(&d, &int(x))])).unwrap(),
            expected.into()
        );
    }
}

#[test]
fn a_multidimensional_boolean_partition_preserves_its_values() {
    let mut rows = Vec::new();
    for a in [false, true] {
        for b in [false, true] {
            rows.push(equation(
                &format!("twoBits{{}}({},{})", boolv(a), boolv(b)),
                &int(i64::from(a ^ b)),
                None,
                "",
            ));
        }
    }
    let d = definition(&rows.join("\n"));
    let summary = Catalog::new(&d)
        .admit(&term(&d, "twoBits{}(A:SortBool{},B:SortBool{})"))
        .unwrap()
        .unwrap();
    assert_eq!(summary.source_rules.len(), 4);
    for a in [false, true] {
        for b in [false, true] {
            let actual = evaluate(&d, &summary, vec![term(&d, &boolv(a)), term(&d, &boolv(b))]);
            assert_eq!(
                crate::builtin::read_int(&actual).unwrap(),
                i64::from(a ^ b).into()
            );
        }
    }
}

#[test]
fn faithful_matching_logic_equalities_are_complementary_total_scalar_tests() {
    let marker = "GUARD:SortBool{}";
    let slot = format!("\\equals{{SortBool{{}},R}}({marker},{})", boolv(true));
    let equal = format!("\\equals{{SortInt{{}},R}}(X:SortInt{{}},{})", int(0));
    let rows = [
        equation("magnitude{}(X:SortInt{})", &int(3), Some(marker), "").replace(&slot, &equal),
        equation("magnitude{}(X:SortInt{})", &int(4), Some(marker), "")
            .replace(&slot, &format!("\\not{{R}}({equal})")),
    ];
    let d = definition(&rows.join("\n"));
    let summary = Catalog::new(&d)
        .admit(&term(&d, "magnitude{}(X:SortInt{})"))
        .unwrap()
        .unwrap();
    for (x, expected) in [(-1, 4), (0, 3), (1, 4)] {
        assert_eq!(
            crate::builtin::read_int(&evaluate(&d, &summary, vec![term(&d, &int(x))])).unwrap(),
            expected.into()
        );
    }
}

#[test]
fn canonical_primitive_domains_discharge_safe_bodies_without_using_branch_guards() {
    let domain = r#"
      hooked-symbol ne{}(SortInt{},SortInt{}) : SortBool{} [function{}(),total{}(),hook{}("INT.ne"),smt-hook{}("distinct")]
      axiom{R} \implies{R}(\top{R}(),\equals{R,R}(
        \ceil{SortInt{},R}(ediv{}(I:SortInt{},D:SortInt{})),
        \and{R}(\equals{SortBool{},R}(ne{}(D:SortInt{},\dv{SortInt{}}("0")),\dv{SortBool{}}("true")),\top{R}()))) [simplification{}()]
    "#;
    let d = definition(
        &[
            domain.to_owned(),
            equation(
                "outer{}(X:SortInt{})",
                &format!("ediv{{}}(X:SortInt{{}},{})", int(32)),
                None,
                "",
            ),
            equation(
                "magnitude{}(X:SortInt{})",
                &format!("ediv{{}}({},X:SortInt{{}})", int(1)),
                Some(&format!("ne{{}}(X:SortInt{{}},{})", int(0))),
                "",
            ),
            equation(
                "magnitude{}(X:SortInt{})",
                &int(0),
                Some(&format!("not{{}}(ne{{}}(X:SortInt{{}},{}))", int(0))),
                "",
            ),
        ]
        .join("\n"),
    );
    assert!(
        Catalog::new(&d)
            .admit(&term(&d, "outer{}(X:SortInt{})"))
            .unwrap()
            .is_ok()
    );
    assert_eq!(
        Catalog::new(&d)
            .admit(&term(&d, "magnitude{}(X:SortInt{})"))
            .unwrap(),
        Err(Rejected::Partial)
    );
}

#[test]
fn malformed_hook_ranks_are_not_read_as_complementary_integer_tests() {
    let d = definition(&[
        "hooked-symbol badLt{}(SortBool{},SortBool{}) : SortBool{} [function{}(),total{}(),hook{}(\"INT.lt\")]".to_owned(),
        "hooked-symbol badGe{}(SortBool{},SortBool{}) : SortBool{} [function{}(),total{}(),hook{}(\"INT.ge\")]".to_owned(),
        equation("bit{}(B:SortBool{})", &int(1), Some(&format!("badLt{{}}(B:SortBool{{}},{})",boolv(true))), ""),
        equation("bit{}(B:SortBool{})", &int(0), Some(&format!("badGe{{}}(B:SortBool{{}},{})",boolv(true))), ""),
    ].join("\n"));
    assert!(
        Catalog::new(&d)
            .admit(&term(&d, "bit{}(B:SortBool{})"))
            .unwrap()
            .is_err()
    );
}

#[test]
fn alpha_renaming_and_limits_do_not_create_free_source_parameters_or_cache_refusals() {
    let d = definition(&equation(
        "outer{}(KRUST-SCALAR-0:SortInt{})",
        &format!("plus{{}}(KRUST-SCALAR-0:SortInt{{}},{})", int(1)),
        None,
        "",
    ));
    let call = term(&d, "outer{}(X:SortInt{})");
    let summary = Catalog::new(&d).admit(&call).unwrap().unwrap();
    let Decision::Value(body) = summary.body.as_ref() else {
        panic!("single equation");
    };
    assert_eq!(
        body.attributes().variables,
        summary.parameters.iter().cloned().collect()
    );
    assert_eq!(
        crate::builtin::read_int(&evaluate(&d, &summary, vec![term(&d, &int(8))])).unwrap(),
        9.into()
    );
    let bit = definition(&bit_rows());
    let mut catalog = Catalog::with_limits(
        &bit,
        Limits {
            rows: 1,
            ..Limits::default()
        },
    );
    assert_eq!(
        catalog.admit(&term(&bit, "bit{}(P:SortBool{})")).unwrap(),
        Err(Rejected::Limit)
    );
    assert!(catalog.active.is_empty() && catalog.rejected.is_empty());
}

#[test]
fn unoffered_predicate_term_equations_prevent_source_coverage_claims() {
    let extra = r#"axiom{R} \implies{R}(\top{R}(),\equals{SortInt{},R}(
        \and{SortInt{}}(bit{}(B:SortBool{}),bit{}(B:SortBool{})),
        \and{SortInt{}}(\dv{SortInt{}}("0"),\top{SortInt{}}()))) [simplification{}()]"#;
    let d = definition(&(bit_rows() + "\n" + extra));
    assert_eq!(
        Catalog::new(&d)
            .admit(&term(&d, "bit{}(B:SortBool{})"))
            .unwrap(),
        Err(Rejected::Unsupported)
    );
}

#[test]
fn known_constructor_specialization_prunes_only_refuted_other_cases_and_allows_aliases() {
    let pred = format!("lt{{}}(X:SortInt{{}},{})", int(0));
    let not = format!("not{{}}({pred})");
    let d = definition(
        &[
            equation("dispatch{}(a{}(),X:SortInt{})", &int(1), Some(&pred), ""),
            equation("dispatch{}(a{}(),X:SortInt{})", &int(2), Some(&not), ""),
            equation(
                "dispatch{}(b{}(),X:SortInt{})",
                "dispatch{}(a{}(),X:SortInt{})",
                None,
                "",
            ),
            equation(
                "dispatch{}(wrap{}(a{}()),X:SortInt{})",
                &format!("ediv{{}}({},{})", int(1), int(0)),
                None,
                "priority{}(\"40\")",
            ),
        ]
        .join("\n"),
    );
    let mut catalog = Catalog::new(&d);
    let a = catalog
        .admit(&term(&d, "dispatch{}(a{}(),V:SortInt{})"))
        .unwrap()
        .unwrap();
    let b = catalog
        .admit(&term(&d, "dispatch{}(b{}(),V:SortInt{})"))
        .unwrap()
        .unwrap();
    assert_eq!(a.source_rules.len(), 2);
    assert_eq!(b.source_rules.len(), 1);
    assert_eq!(b.dependencies, BTreeSet::from([a.key.clone()]));
    assert_ne!(a.key, b.key);
    assert_eq!(
        catalog
            .admit(&term(&d, "dispatch{}(OP:SortOp{},V:SortInt{})"))
            .unwrap(),
        Err(Rejected::Unsupported)
    );
}

#[test]
fn missing_overlapping_restricted_unbound_and_partial_rows_do_not_become_summaries() {
    let zero = int(0);
    let one = int(1);
    let true_lhs = format!("bit{{}}({})", boolv(true));
    let false_lhs = format!("bit{{}}({})", boolv(false));
    let cases = [
        (equation(&true_lhs, &one, None, ""), Rejected::Incomplete),
        (
            [
                bit_rows(),
                equation("bit{}(B:SortBool{})", &int(2), None, ""),
            ]
            .join("\n"),
            Rejected::Overlapping,
        ),
        (
            [
                equation(&true_lhs, &one, None, "concrete{}()"),
                equation(&false_lhs, &zero, None, ""),
            ]
            .join("\n"),
            Rejected::Restricted,
        ),
        (
            [
                equation(&true_lhs, &one, None, "priority{}(\"40\")"),
                equation(&false_lhs, &zero, None, ""),
            ]
            .join("\n"),
            Rejected::Restricted,
        ),
        (
            [
                equation(&true_lhs, "FREE:SortInt{}", None, ""),
                equation(&false_lhs, &zero, None, ""),
            ]
            .join("\n"),
            Rejected::Restricted,
        ),
        (
            [
                equation(&true_lhs, &one, None, ""),
                equation(&false_lhs, &format!("ediv{{}}({one},{zero})"), None, ""),
            ]
            .join("\n"),
            Rejected::Partial,
        ),
    ];
    for (rules, expected) in cases {
        let d = definition(&rules);
        let result = Catalog::new(&d)
            .admit(&term(&d, "bit{}(P:SortBool{})"))
            .unwrap();
        assert_eq!(result, Err(expected), "{rules}");
    }
}

#[test]
fn simplification_and_wildcard_equations_are_not_omitted_from_the_source_catalog() {
    for extra in [
        equation("bit{}(B:SortBool{})", &int(2), None, "simplification{}()"),
        equation("ANY:SortInt{}", &int(3), None, "simplification{}()"),
    ] {
        let d = definition(&(bit_rows() + "\n" + &extra));
        assert!(
            Catalog::new(&d)
                .admit(&term(&d, "bit{}(P:SortBool{})"))
                .unwrap()
                .is_err(),
            "{extra}"
        );
    }
}

#[test]
fn dependency_cycles_and_transitive_effects_are_rejected() {
    let d = definition(
        &[
            equation(
                "outer{}(X:SortInt{})",
                &format!("plus{{}}(outer{{}}(X:SortInt{{}}),{})", int(1)),
                None,
                "",
            ),
            equation("dispatch{}(a{}(),X:SortInt{})", "effect{}()", None, ""),
        ]
        .join("\n"),
    );
    assert_eq!(
        Catalog::new(&d)
            .admit(&term(&d, "outer{}(X:SortInt{})"))
            .unwrap(),
        Err(Rejected::Recursive)
    );
    assert_eq!(
        Catalog::new(&d)
            .admit(&term(&d, "dispatch{}(a{}(),X:SortInt{})"))
            .unwrap(),
        Err(Rejected::Unsupported)
    );
}

#[test]
fn changing_static_arguments_is_bounded_and_not_mistaken_for_termination() {
    let d = definition(&equation(
        "dispatch{}(OP:SortOp{},X:SortInt{})",
        "dispatch{}(wrap{}(OP:SortOp{}),X:SortInt{})",
        None,
        "",
    ));
    let mut catalog = Catalog::with_limits(
        &d,
        Limits {
            specializations: 5,
            ..Limits::default()
        },
    );
    assert_eq!(
        catalog
            .admit(&term(&d, "dispatch{}(a{}(),X:SortInt{})"))
            .unwrap(),
        Err(Rejected::Limit)
    );
    assert!(catalog.active.is_empty());
    assert!(catalog.rejected.is_empty());
}

#[test]
fn cancellation_is_propagated_without_poisoning_the_catalog() {
    let d = definition(&bit_rows());
    let mut catalog = Catalog::new(&d);
    let call = term(&d, "bit{}(P:SortBool{})");
    let token = crate::stop::CancellationToken::new();
    token.cancel();
    let stop = token.scope(|| catalog.admit(&call)).unwrap_err();
    assert_eq!(stop.into_cause(), crate::stop::StopCause::Cancelled);
    assert!(
        catalog.accepted.is_empty() && catalog.rejected.is_empty() && catalog.active.is_empty()
    );
    assert!(catalog.admit(&call).unwrap().is_ok());
}

#[test]
fn source_mutants_have_separate_metadata_and_changed_decisions() {
    let d1 = definition(&bit_rows());
    let d2 = definition(&bit_rows().replace(&int(1), &int(7)));
    let a = Catalog::new(&d1)
        .admit(&term(&d1, "bit{}(P:SortBool{})"))
        .unwrap()
        .unwrap();
    let b = Catalog::new(&d2)
        .admit(&term(&d2, "bit{}(P:SortBool{})"))
        .unwrap()
        .unwrap();
    assert_eq!(a.key, b.key);
    assert_ne!(a.body, b.body);
    assert_ne!(a.source_rules, b.source_rules);
}

/// An explicit development probe over a real compiler artifact. The ordinary tests remain
/// self-contained; this does not turn a hand-authored KORE fixture into authoring qualification.
#[test]
#[ignore = "set SUMMARY_AUDIT_KORE to the compiled Foldiboy operation audit"]
fn compiled_foldiboy_equations_are_admitted_without_source_rewrites() {
    let path = std::env::var("SUMMARY_AUDIT_KORE").expect("compiled audit artifact");
    let source = std::fs::read_to_string(path).unwrap();
    let d =
        BackendDefinition::internalize(&parse_definition(&source).unwrap(), "OPERATION-AUDIT-SPEC")
            .unwrap();
    let mut catalog = Catalog::new(&d);
    for source in [
        "LblflagBit{}(B:SortBool{})",
        "Lblflags{}(Z:SortBool{},N:SortBool{},H:SortBool{},C:SortBool{})",
        "LblcarryIn{}(F:SortInt{})",
        "Lblsigned{}(V:SortInt{})",
        "LblunaryResult{}(LblunaryDaa{}(),V:SortInt{},F:SortInt{})",
        "LblunaryResult{}(LblunaryRlca{}(),V:SortInt{},F:SortInt{})",
        "LblunaryResult{}(LblunarySra{}(),V:SortInt{},F:SortInt{})",
        "LblunaryFlags{}(LblunaryDaa{}(),V:SortInt{},F:SortInt{})",
        "LblaluFlags{}(LblaluAdc{}(),A:SortInt{},B:SortInt{},F:SortInt{})",
        "LblaluResult{}(LblaluOr{}(),A:SortInt{},B:SortInt{},F:SortInt{})",
        r#"LblunaryResult{}(LblunarySetBit{}(\dv{SortInt{}}("0")),V:SortInt{},F:SortInt{})"#,
    ] {
        let summary = catalog
            .admit(&term(&d, source))
            .unwrap()
            .unwrap_or_else(|e| panic!("{source}: {e:?}"));
        eprintln!(
            "{source}: rows={} dependencies={}",
            summary.source_rules.len(),
            summary.dependencies.len()
        );
    }
    eprintln!(
        "specializations={} remaining_work={}",
        catalog.accepted.len(),
        catalog.remaining
    );
}
