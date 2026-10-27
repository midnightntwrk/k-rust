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
            "bit" | "testBit" => vec!["SortBool"],
            "twoBits" => vec!["SortBool", "SortBool"],
            "choose" | "chooseBool" | "nested" | "totalChoose" | "strictChoose" => {
                vec!["SortBool", "SortInt", "SortInt"]
            }
            "ignore" => vec!["SortInt"],
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

fn compound_guard_rows(hook: &str) -> String {
    let connectives = format!(
        r#"
      hooked-symbol both{{}}(SortBool{{}},SortBool{{}}) : SortBool{{}}
        [function{{}}(),total{{}}(),hook{{}}("{hook}")]
    "#
    );
    [
        connectives,
        equation(
            "twoBits{}(P:SortBool{},Q:SortBool{})",
            &int(1),
            Some("P:SortBool{}"),
            "",
        ),
        equation(
            "twoBits{}(P:SortBool{},Q:SortBool{})",
            &int(2),
            Some("both{}(not{}(P:SortBool{}),Q:SortBool{})"),
            "",
        ),
        equation(
            "twoBits{}(P:SortBool{},Q:SortBool{})",
            &int(0),
            Some("both{}(not{}(P:SortBool{}),not{}(Q:SortBool{}))"),
            "",
        ),
    ]
    .join("\n")
}

#[test]
fn compound_boolean_path_guards_form_their_actual_source_partition() {
    for hook in ["BOOL.and", "BOOL.andThen"] {
        let d = definition(&compound_guard_rows(hook));
        let summary = Catalog::new(&d)
            .admit(&term(&d, "twoBits{}(P:SortBool{},Q:SortBool{})"))
            .unwrap()
            .unwrap();
        assert_eq!(summary.source_rules.len(), 3);
        for p in [false, true] {
            for q in [false, true] {
                assert_eq!(
                    evaluate(&d, &summary, vec![Term::bool(p), Term::bool(q)]),
                    Term::int(if p {
                        1
                    } else if q {
                        2
                    } else {
                        0
                    })
                );
            }
        }
    }
    let incomplete = compound_guard_rows("BOOL.andThen");
    let incomplete = incomplete
        .lines()
        .filter(|line| !line.contains("not{}(Q:SortBool{})"))
        .collect::<Vec<_>>()
        .join("\n");
    let d = definition(&incomplete);
    assert_eq!(
        Catalog::new(&d)
            .admit(&term(&d, "twoBits{}(P:SortBool{},Q:SortBool{})"))
            .unwrap(),
        Err(Rejected::Incomplete)
    );
    // The same spelling with a changed source hook has a different truth table: these
    // rows then really overlap. A name or a total declaration does not supply conjunction.
    let d = definition(&compound_guard_rows("BOOL.orElse"));
    assert_eq!(
        Catalog::new(&d)
            .admit(&term(&d, "twoBits{}(P:SortBool{},Q:SortBool{})"))
            .unwrap(),
        Err(Rejected::Overlapping)
    );
    let text = compound_guard_rows("BOOL.andThen").replace(
        "total{}(),hook{}(\"BOOL.andThen\")",
        "total{}(),impure{}(),hook{}(\"BOOL.andThen\")",
    );
    let d = definition(&text);
    assert_eq!(
        Catalog::new(&d)
            .admit(&term(&d, "twoBits{}(P:SortBool{},Q:SortBool{})"))
            .unwrap(),
        Err(Rejected::Unsupported)
    );
}

#[test]
fn compound_guard_complements_keep_both_boolean_polarities() {
    for hook in ["BOOL.and", "BOOL.andThen", "BOOL.or", "BOOL.orElse"] {
        let rows = format!(
            r#"hooked-symbol both{{}}(SortBool{{}},SortBool{{}}) : SortBool{{}} [function{{}}(),total{{}}(),hook{{}}("{hook}")]"#
        );
        let guard = "both{}(P:SortBool{},Q:SortBool{})";
        let d = definition(
            &[
                rows,
                equation(
                    "twoBits{}(P:SortBool{},Q:SortBool{})",
                    &int(1),
                    Some(guard),
                    "",
                ),
                equation(
                    "twoBits{}(P:SortBool{},Q:SortBool{})",
                    &int(0),
                    Some(&format!("not{{}}({guard})")),
                    "",
                ),
            ]
            .join("\n"),
        );
        let summary = Catalog::new(&d)
            .admit(&term(&d, "twoBits{}(P:SortBool{},Q:SortBool{})"))
            .unwrap()
            .unwrap();
        for p in [false, true] {
            for q in [false, true] {
                let expected = if matches!(hook, "BOOL.and" | "BOOL.andThen") {
                    p && q
                } else {
                    p || q
                };
                assert_eq!(
                    evaluate(&d, &summary, vec![Term::bool(p), Term::bool(q)]),
                    Term::int(i64::from(expected))
                );
            }
        }
    }
}

#[test]
fn contradictory_boolean_guards_do_not_overlap_an_unconditional_row() {
    let d = definition(
        &[
            r#"hooked-symbol both{}(SortBool{},SortBool{}) : SortBool{} [function{}(),total{}(),hook{}("BOOL.andThen")]"#.to_owned(),
            equation("twoBits{}(P:SortBool{},Q:SortBool{})", &int(1), None, ""),
            equation(
                "twoBits{}(P:SortBool{},Q:SortBool{})",
                &int(0),
                Some("both{}(P:SortBool{},not{}(P:SortBool{}))"),
                "",
            ),
        ]
        .join("\n"),
    );
    let summary = Catalog::new(&d)
        .admit(&term(&d, "twoBits{}(P:SortBool{},Q:SortBool{})"))
        .unwrap()
        .unwrap();
    for p in [false, true] {
        assert_eq!(
            evaluate(&d, &summary, vec![Term::bool(p), Term::bool(false)]),
            Term::int(1)
        );
    }
}

#[test]
fn shared_compound_guards_stop_at_the_work_allowance() {
    let d = definition(&compound_guard_rows("BOOL.andThen"));
    let head = d.symbols()["both"].clone();
    let mut guard = term(&d, "P:SortBool{}");
    for _ in 0..30 {
        guard = Term::application(head.clone(), vec![], vec![guard.clone(), guard]);
    }
    let mut work = 128;
    assert!(matches!(
        term_guard(&guard, true, &mut work, 0, 64).unwrap(),
        Err(Rejected::Limit)
    ));
    assert_eq!(work, 0);
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
    let guarded = Catalog::new(&d)
        .admit(&term(&d, "magnitude{}(X:SortInt{})"))
        .unwrap()
        .unwrap();
    assert!(guarded.declared_total);
    assert!(
        !guarded.domain_total,
        "the nonzero caller/branch guard is not global totality metadata"
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

fn emission_state(
    d: &BackendDefinition,
    known: &[Predicate],
    checked: &[Predicate],
) -> super::super::TranslationState {
    let mut state = super::super::TranslationState::new();
    state.congruence = super::super::CongruencePolicy::from_definition(d).map(Arc::new);
    super::prepare(
        &super::Source::new(d),
        &mut state,
        known,
        &crate::substitution::Substitution::new(),
        checked,
    )
    .unwrap()
    .unwrap();
    state
}

#[test]
fn actual_scalar_emission_shares_dependencies_and_keeps_actual_operand_admission() {
    let outer = equation(
        "outer{}(X:SortInt{})",
        "plus{}(bit{}(\\dv{SortBool{}}(\"true\")),X:SortInt{})",
        None,
        "",
    );
    let d = definition(&(bit_rows() + &outer));
    let call = term(&d, "outer{}(X:SortInt{})");
    let checked = Predicate::Equals(
        call.clone(),
        term(&d, r#"plus{}(X:SortInt{},\dv{SortInt{}}("1"))"#),
    );
    let mut state = emission_state(&d, &[], &[checked]);
    assert_eq!(state.summaries.len(), 2);
    assert_eq!(state.derived_definitions.len(), 2);
    let emitted = state.translate_term(&call).unwrap().to_string();
    assert!(emitted.contains("SMT-"));
    assert_eq!(state.exactness(), super::super::Exactness::Exact);
    // Reusing the exact same signature cannot admit a set-valued actual argument.
    let set = Term::variable(Variable::set("Set", Sort::simple("SortInt")));
    let TermKind::Application { symbol, .. } = call.kind() else {
        unreachable!()
    };
    let set_call = Term::application(symbol.clone(), vec![], vec![set]);
    let reading = super::reading(&state.summaries, &set_call)
        .unwrap()
        .name
        .clone();
    let refused = state.translate_term(&set_call).unwrap().to_string();
    assert!(!refused.contains(&format!("({reading} ")));
    assert_eq!(state.exactness(), super::super::Exactness::Approximate);
}

#[cfg(feature = "z3")]
#[test]
fn scalar_function_parameters_are_local_under_nested_quantifiers() {
    use crate::smt::{SmtSolver, Validity, Z3Solver};
    let d = definition(&bit_rows());
    let b = Variable::new("B", Sort::simple("SortBool"));
    let p = Predicate::Forall(
        b,
        Arc::new(Predicate::Term(term(
            &d,
            r#"ge{}(bit{}(B:SortBool{}),\dv{SortInt{}}("0"))"#,
        ))),
    );
    let q = super::super::SmtPrelude::from_definition(&d)
        .unwrap()
        .query(
            &[],
            &crate::substitution::Substitution::new(),
            std::slice::from_ref(&p),
            false,
        )
        .unwrap()
        .unwrap();
    assert!(!q.base().contains("declare-const"), "{}", q.base());
    assert!(q.base().contains("define-fun"));
    assert_eq!(
        Z3Solver::new(&d).unwrap().check_predicates(
            &[],
            &crate::substitution::Substitution::new(),
            &[p]
        ),
        Ok(Ok(Validity::Valid))
    );
}

#[cfg(feature = "z3")]
#[test]
fn native_models_and_mutants_read_the_actual_finite_source() {
    use crate::smt::{SmtSolver, Validity, Z3Solver};
    let baseline = definition(&bit_rows());
    let changed = definition(&bit_rows().replace(&int(0), &int(2)));
    let claim = |d: &BackendDefinition| {
        Predicate::Equals(
            term(d, &format!("bit{{}}({})", boolv(false))),
            term(d, &int(0)),
        )
    };
    assert_eq!(
        Z3Solver::new(&baseline).unwrap().check_predicates(
            &[],
            &crate::substitution::Substitution::new(),
            &[claim(&baseline)]
        ),
        Ok(Ok(Validity::Valid))
    );
    assert_eq!(
        Z3Solver::new(&changed).unwrap().check_predicates(
            &[],
            &crate::substitution::Substitution::new(),
            &[claim(&changed)]
        ),
        Ok(Ok(Validity::Refuted))
    );
}

#[cfg(feature = "z3")]
fn mixed_source() -> String {
    let extra = r#"
      hooked-symbol bor{}(SortInt{},SortInt{}):SortInt{} [function{}(),total{}(),hook{}("INT.or"),smtlib{}("orInt")]
      hooked-symbol band{}(SortInt{},SortInt{}):SortInt{} [function{}(),total{}(),hook{}("INT.and"),smtlib{}("andInt")]
      symbol mix{}(SortInt{},SortInt{}):SortInt{} [function{}(),total{}()]
    "#;
    format!(
        "{extra}{}",
        equation(
            "mix{}(X:SortInt{},Y:SortInt{})",
            "plus{}(bor{}(X:SortInt{},Y:SortInt{}),band{}(X:SortInt{},Y:SortInt{}))",
            None,
            "simplification{}()"
        )
    )
}

#[cfg(feature = "z3")]
fn range(d: &BackendDefinition, name: &str, upper: i64) -> Vec<Predicate> {
    vec![
        Predicate::Term(term(d, &format!("ge{{}}({name}:SortInt{{}},{})", int(0)))),
        Predicate::Term(term(
            d,
            &format!("lt{{}}({name}:SortInt{{}},{})", int(upper)),
        )),
    ]
}

#[cfg(feature = "z3")]
#[test]
fn shared_word_variants_compose_with_independent_arithmetic_under_native_defaults() {
    use crate::smt::{SmtSolver, Validity, Z3Solver};
    let d = definition(&mixed_source());
    for width in [8, 16] {
        let known = range(&d, "X", 1 << width)
            .into_iter()
            .chain(range(&d, "Y", 1 << width))
            .collect::<Vec<_>>();
        let claim = Predicate::Equals(
            term(&d, "mix{}(X:SortInt{},Y:SortInt{})"),
            term(&d, "plus{}(X:SortInt{},Y:SortInt{})"),
        );
        let q = super::super::SmtPrelude::from_definition(&d)
            .unwrap()
            .query(
                &known,
                &crate::substitution::Substitution::new(),
                std::slice::from_ref(&claim),
                false,
            )
            .unwrap()
            .unwrap();
        assert!(q.base().contains("define-fun-rec SMT-WORD"), "{}", q.base());
        assert!(q.checked().to_string().contains("SMT-WORD-"));
        assert!(q.model_mappings().is_none());
        let counters = k_rust_kore::measure::snapshot();
        let started = std::time::Instant::now();
        let result = Z3Solver::new(&d).unwrap().check_predicates(
            &known,
            &crate::substitution::Substitution::new(),
            &[claim],
        );
        let costs = k_rust_kore::measure::snapshot().delta(&counters);
        eprintln!(
            "summary-word-{width}: {result:?}; elapsed={:?}; script_bytes={}; runs={}; resource_units={}",
            started.elapsed(),
            q.base().len() + q.checked().to_string().len(),
            costs.get(k_rust_kore::measure::Counter::SmtSolverRuns),
            costs.get(k_rust_kore::measure::Counter::SmtRlimitCount)
        );
        assert_eq!(result, Ok(Ok(Validity::Valid)));
    }
}

#[cfg(feature = "z3")]
#[test]
fn distinct_argument_dependency_diamonds_share_integer_and_word_definitions() {
    let mut extra = String::from(
        r#"hooked-symbol band{}(SortInt{},SortInt{}):SortInt{} [function{}(),total{}(),hook{}("INT.and")]
    "#,
    );
    for level in 0..=30 {
        extra.push_str(&format!(
            "symbol stage{level}{{}}(SortInt{{}}):SortInt{{}} [function{{}}(),total{{}}()]\n"
        ));
        let rhs = if level == 0 {
            "X:SortInt{}".to_owned()
        } else {
            format!(
                "plus{{}}(stage{}{{}}(band{{}}(plus{{}}(X:SortInt{{}},{}),{})),stage{}{{}}(band{{}}(plus{{}}(X:SortInt{{}},{}),{})))",
                level - 1,
                int(1),
                int(255),
                level - 1,
                int(2),
                int(255)
            )
        };
        extra.push_str(&equation(
            &format!("stage{level}{{}}(X:SortInt{{}})"),
            &rhs,
            None,
            "simplification{}()",
        ));
    }
    let d = definition(&extra);
    let call = term(&d, "stage30{}(X:SortInt{})");
    let claim = Predicate::Equals(call.clone(), call);
    let started = std::time::Instant::now();
    let q = super::super::SmtPrelude::from_definition(&d)
        .unwrap()
        .query(
            &range(&d, "X", 256),
            &crate::substitution::Substitution::new(),
            std::slice::from_ref(&claim),
            false,
        )
        .unwrap()
        .unwrap();
    let script = format!("{}\n(assert {})", q.base(), q.checked());
    assert_eq!(script.matches("define-fun").count(), 62);
    assert!(script.len() < 64_000, "{}", script.len());
    use crate::smt::{Satisfiability, SmtSolver, Z3Solver};
    let mut known = range(&d, "X", 256);
    known.push(claim);
    assert_eq!(
        Z3Solver::new(&d)
            .unwrap()
            .is_sat(&known, &crate::substitution::Substitution::new()),
        Ok(Ok(Satisfiability::Sat))
    );
    eprintln!(
        "summary distinct-argument diamond: {} bytes, {:?}",
        script.len(),
        started.elapsed()
    );
}

#[cfg(feature = "z3")]
#[test]
fn actual_model_queries_preserve_exact_helper_and_opaque_fallback_boundaries() {
    use crate::{
        model::model_of,
        smt::{ModelResult, Z3Solver},
    };
    let d = definition(&bit_rows());
    let predicate = Predicate::Equals(term(&d, "bit{}(B:SortBool{})"), term(&d, &int(1)));
    let result = model_of(&d, &predicate, &Z3Solver::new(&d).unwrap())
        .unwrap()
        .unwrap();
    let ModelResult::Sat(values) = result else {
        panic!("{result:?}")
    };
    let b = Variable::new("B", Sort::simple("SortBool"));
    assert!(values.contains_key(&b));
    let summary = Catalog::new(&d)
        .admit(&term(&d, "bit{}(B:SortBool{})"))
        .unwrap()
        .unwrap();
    let value = evaluate(&d, &summary, vec![values[&b].clone()]);
    assert_eq!(crate::builtin::read_int(&value).unwrap(), 1.into());
    let d = definition(&mixed_source());
    let predicates = range(&d, "X", 256)
        .into_iter()
        .chain(range(&d, "Y", 256))
        .chain([Predicate::Equals(
            term(&d, "mix{}(X:SortInt{},Y:SortInt{})"),
            term(&d, &int(17)),
        )])
        .collect::<Vec<_>>();
    let result = model_of(
        &d,
        &Predicate::And(predicates.into()),
        &Z3Solver::new(&d).unwrap(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        result,
        ModelResult::Unknown(super::super::APPROXIMATE_MODEL_REASON.to_owned())
    );
}

#[cfg(feature = "z3")]
#[test]
fn exact_range_profiles_are_query_local_and_source_ownership_outlives_the_loader() {
    use crate::smt::{SmtSolver, Validity, Z3Solver};
    let d = definition(&mixed_source());
    let a = Predicate::Equals(
        term(&d, "mix{}(X:SortInt{},X:SortInt{})"),
        term(&d, "mix{}(Y:SortInt{},Y:SortInt{})"),
    );
    let known = range(&d, "X", 255)
        .into_iter()
        .chain(range(&d, "Y", 256))
        .collect::<Vec<_>>();
    let q = super::super::SmtPrelude::from_definition(&d)
        .unwrap()
        .query(
            &known,
            &crate::substitution::Substitution::new(),
            &[a],
            false,
        )
        .unwrap()
        .unwrap();
    assert_eq!(q.base().matches("define-fun-rec SMT-WORD-").count(), 2);
    let solver = {
        let d = definition(&bit_rows());
        Z3Solver::new(&d).unwrap()
    };
    let claim = Predicate::Equals(
        term(
            &definition(&bit_rows()),
            &format!("bit{{}}({})", boolv(true)),
        ),
        Term::raw_domain_value(Sort::simple("SortInt"), "1"),
    );
    assert_eq!(
        solver.check_predicates(&[], &crate::substitution::Substitution::new(), &[claim]),
        Ok(Ok(Validity::Valid))
    );
}

#[cfg(feature = "z3")]
#[test]
#[ignore = "set SUMMARY_AUDIT_KORE to the compiled Foldiboy operation audit"]
fn compiled_foldiboy_shared_emission_uses_original_helper_bodies() {
    use crate::smt::{Satisfiability, SmtSolver, Z3Solver};
    let path = std::env::var("SUMMARY_AUDIT_KORE").unwrap();
    let source = std::fs::read_to_string(path).unwrap();
    let d =
        BackendDefinition::internalize(&parse_definition(&source).unwrap(), "OPERATION-AUDIT-SPEC")
            .unwrap();
    let started = std::time::Instant::now();
    let snapshot = super::Source::new(&d);
    let snapshot_cost = started.elapsed();
    let scalar = |name: &str| term(&d, &format!("{name}:SortInt{{}}"));
    let mut known = Vec::new();
    for name in ["A", "B", "V", "F"] {
        for (hook, n) in [("INT.ge", 0), ("INT.lt", 256)] {
            let symbol = d
                .symbols()
                .values()
                .find(|s| {
                    s.attributes.hook.as_deref() == Some(hook)
                        && s.argument_sorts
                            .iter()
                            .all(|s| s.is_builtin(BuiltinSort::Int))
                })
                .unwrap();
            known.push(Predicate::Term(Term::application(
                symbol.clone(),
                vec![],
                vec![scalar(name), term(&d, &int(n))],
            )));
        }
    }
    let mut checked = Vec::new();
    for source in [
        "LblflagBit{}(P:SortBool{})",
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
        let call = term(&d, source);
        checked.push(Predicate::Equals(call.clone(), call));
    }
    let mut state = super::super::TranslationState::new();
    state.congruence = super::super::CongruencePolicy::from_definition(&d).map(Arc::new);
    let started = std::time::Instant::now();
    super::prepare(
        &snapshot,
        &mut state,
        &known,
        &crate::substitution::Substitution::new(),
        &checked,
    )
    .unwrap()
    .unwrap();
    assert_eq!(state.summaries.len(), 19);
    let scalar_cost = started.elapsed();
    let started = std::time::Instant::now();
    let prelude = super::super::SmtPrelude::from_definition(&d).unwrap();
    assert_eq!(prelude, prelude.clone());
    let query = prelude
        .query(
            &known,
            &crate::substitution::Substitution::new(),
            &checked,
            false,
        )
        .unwrap()
        .unwrap();
    let cost = started.elapsed();
    let super::super::SExpr::List(expressions) = query.checked() else {
        panic!("checked conjunction")
    };
    for (index, expression) in expressions.iter().skip(1).enumerate() {
        let super::super::SExpr::List(parts) = expression else {
            panic!("scalar atom")
        };
        assert_eq!(
            parts.first(),
            Some(&super::super::SExpr::atom("ite")),
            "actual helper {index}: {expression}"
        );
    }
    let bytes = query.base().len() + query.checked().to_string().len();
    let mut predicates = known;
    predicates.extend(checked);
    let started = std::time::Instant::now();
    assert_eq!(
        Z3Solver::new(&d)
            .unwrap()
            .is_sat(&predicates, &crate::substitution::Substitution::new()),
        Ok(Ok(Satisfiability::Sat))
    );
    eprintln!(
        "actual Foldiboy emission: snapshot={snapshot_cost:?} scalar={scalar_cost:?} complete={cost:?} native={:?} scalar_variants={} word_variants={} bytes={bytes}",
        started.elapsed(),
        state.summaries.len(),
        query.base().matches("define-fun-rec SMT-WORD-").count()
    );
}

#[test]
fn query_emission_cancellation_propagates_and_does_not_poison_source_ownership() {
    let d = definition(&bit_rows());
    let source = super::Source::new(&d);
    let checked = [Predicate::Equals(
        term(&d, "bit{}(B:SortBool{})"),
        term(&d, &int(1)),
    )];
    let token = crate::stop::CancellationToken::new();
    token.cancel();
    let mut state = super::super::TranslationState::new();
    state.congruence = super::super::CongruencePolicy::from_definition(&d).map(Arc::new);
    let result = token.scope(|| {
        super::prepare(
            &source,
            &mut state,
            &[],
            &crate::substitution::Substitution::new(),
            &checked,
        )
    });
    assert_eq!(
        result.unwrap_err().into_cause(),
        crate::stop::StopCause::Cancelled
    );
    assert!(state.summaries.is_empty());
    super::prepare(
        &source,
        &mut state,
        &[],
        &crate::substitution::Substitution::new(),
        &checked,
    )
    .unwrap()
    .unwrap();
    assert_eq!(state.summaries.len(), 1);
}

fn partial_source() -> String {
    let declarations = r#"
      symbol choose{}(SortBool{},SortInt{},SortInt{}) : SortInt{} [function{}()]
      symbol chooseBool{}(SortBool{},SortInt{},SortInt{}) : SortBool{} [function{}()]
      symbol nested{}(SortBool{},SortInt{},SortInt{}) : SortInt{} [function{}()]
      symbol totalChoose{}(SortBool{},SortInt{},SortInt{}) : SortInt{} [function{}(),total{}()]
      symbol strictChoose{}(SortBool{},SortInt{},SortInt{}) : SortInt{} [function{}()]
      symbol ignore{}(SortInt{}) : SortInt{} [function{}()]
      hooked-symbol select{}(SortBool{},SortInt{},SortInt{}) : SortInt{}
        [function{}(),total{}(),hook{}("KEQUAL.ite"),smt-hook{}("ite")]
      hooked-symbol ne{}(SortInt{},SortInt{}) : SortBool{}
        [function{}(),total{}(),hook{}("INT.ne"),smt-hook{}("distinct")]
      axiom{R} \implies{R}(\top{R}(),\equals{R,R}(
        \ceil{SortInt{},R}(ediv{}(I:SortInt{},D:SortInt{})),
        \and{R}(\equals{SortBool{},R}(ne{}(D:SortInt{},\dv{SortInt{}}("0")),\dv{SortBool{}}("true")),\top{R}()))) []
    "#;
    let mut rows = vec![declarations.to_owned()];
    for head in ["choose", "totalChoose"] {
        rows.push(equation(
            &format!("{head}{{}}({},X:SortInt{{}},Y:SortInt{{}})", boolv(true)),
            "ediv{}(X:SortInt{},Y:SortInt{})",
            None,
            "",
        ));
        rows.push(equation(
            &format!("{head}{{}}({},X:SortInt{{}},Y:SortInt{{}})", boolv(false)),
            &int(0),
            None,
            "",
        ));
    }
    for (b, body) in [
        (
            true,
            format!("ge{{}}(ediv{{}}(X:SortInt{{}},Y:SortInt{{}}),{})", int(0)),
        ),
        (false, boolv(false)),
    ] {
        rows.push(
            equation(
                &format!("chooseBool{{}}({},X:SortInt{{}},Y:SortInt{{}})", boolv(b)),
                &body,
                None,
                "",
            )
            .replace("\\equals{SortInt{},R}", "\\equals{SortBool{},R}")
            .replace("\\and{SortInt{}}", "\\and{SortBool{}}")
            .replace("\\top{SortInt{}}", "\\top{SortBool{}}"),
        );
    }
    rows.push(equation("ignore{}(X:SortInt{})", &int(0), None, ""));
    rows.push(equation(
        "nested{}(B:SortBool{},X:SortInt{},Y:SortInt{})",
        "choose{}(B:SortBool{},ediv{}(X:SortInt{},Y:SortInt{}),Y:SortInt{})",
        None,
        "",
    ));
    rows.push(equation(
        "strictChoose{}(B:SortBool{},X:SortInt{},Y:SortInt{})",
        &format!(
            "select{{}}(B:SortBool{{}},ediv{{}}(X:SortInt{{}},Y:SortInt{{}}),{})",
            int(0)
        ),
        None,
        "",
    ));
    source(&rows.join("\n"))
}

#[cfg(feature = "z3")]
#[test]
fn partial_helper_domains_follow_the_selected_source_branch_and_keep_every_call_argument() {
    use crate::{
        smt::{SmtSolver, Validity, Z3Solver},
        substitution::Substitution,
    };
    let d = BackendDefinition::internalize(&parse_definition(&partial_source()).unwrap(), "MAIN")
        .unwrap();
    let solver = Z3Solver::new(&d).unwrap();
    let call = |head: &str, b: bool, x: i64, y: i64| {
        term(
            &d,
            &format!("{head}{{}}({},{},{})", boolv(b), int(x), int(y)),
        )
    };
    for (value, defined) in [
        (call("choose", false, 6, 0), true),
        (call("choose", true, 6, 0), false),
        (call("choose", true, 6, 2), true),
        (call("strictChoose", false, 6, 0), false),
        (call("nested", false, 6, 0), false),
        (call("nested", true, 8, 2), true),
        (
            term(
                &d,
                &format!(
                    "ignore{{}}(choose{{}}({},{},{}))",
                    boolv(true),
                    int(6),
                    int(0)
                ),
            ),
            false,
        ),
    ] {
        let domain = Predicate::Ceil(value.clone());
        let expected = if defined {
            domain
        } else {
            Predicate::Not(Arc::new(domain))
        };
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &[expected]),
            Ok(Ok(Validity::Valid)),
            "{value:?}"
        );
    }
    for (value, result) in [
        (call("choose", false, 6, 0), 0),
        (call("choose", true, 6, 2), 3),
        (call("nested", true, 8, 2), 2),
    ] {
        assert_eq!(
            solver.check_predicates(
                &[],
                &Substitution::new(),
                &[Predicate::Equals(value, term(&d, &int(result)))]
            ),
            Ok(Ok(Validity::Valid))
        );
    }
}

#[cfg(feature = "z3")]
#[test]
fn total_helper_declarations_keep_totality_and_an_opaque_value_outside_the_source_safe_region() {
    use crate::{
        smt::{Exactness, SmtPrelude, SmtSolver, Validity, Z3Solver},
        substitution::Substitution,
    };
    let d = BackendDefinition::internalize(&parse_definition(&partial_source()).unwrap(), "MAIN")
        .unwrap();
    let solver = Z3Solver::new(&d).unwrap();
    let call = term(
        &d,
        &format!("totalChoose{{}}({},{},{})", boolv(true), int(6), int(0)),
    );
    assert_eq!(
        solver.check_predicates(&[], &Substitution::new(), &[Predicate::Ceil(call.clone())]),
        Ok(Ok(Validity::Valid))
    );
    let checked = [Predicate::Equals(call, term(&d, &int(99)))];
    assert_eq!(
        solver.check_predicates(&[], &Substitution::new(), &checked),
        Ok(Ok(Validity::Contingent))
    );
    let query = SmtPrelude::from_definition(&d)
        .unwrap()
        .query(&[], &Substitution::new(), &checked, true)
        .unwrap()
        .unwrap();
    assert_eq!(query.exactness(), Exactness::Approximate);
    assert!(query.model_mappings().is_none());
    let safe = term(
        &d,
        &format!("totalChoose{{}}({},{},{})", boolv(true), int(6), int(2)),
    );
    assert_eq!(
        solver.check_predicates(
            &[],
            &Substitution::new(),
            &[Predicate::Equals(safe, term(&d, &int(3)))]
        ),
        Ok(Ok(Validity::Valid))
    );
}

#[cfg(feature = "z3")]
#[test]
fn partial_helper_mutations_and_explicit_domain_rows_keep_their_actual_source_meaning() {
    use crate::{
        smt::{SmtSolver, Validity, Z3Solver},
        substitution::Substitution,
    };
    let baseline = partial_source();
    let changed = baseline.replace(
        "ediv{}(X:SortInt{},Y:SortInt{})",
        &format!(
            "ediv{{}}(X:SortInt{{}},plus{{}}(Y:SortInt{{}},{}) )",
            int(1)
        ),
    );
    for (source, expected, defined_at_zero) in [(&baseline, 3, false), (&changed, 2, true)] {
        let d = BackendDefinition::internalize(&parse_definition(source).unwrap(), "MAIN").unwrap();
        let solver = Z3Solver::new(&d).unwrap();
        let value = term(
            &d,
            &format!("choose{{}}({},{},{})", boolv(true), int(6), int(2)),
        );
        assert_eq!(
            solver.check_predicates(
                &[],
                &Substitution::new(),
                &[Predicate::Equals(value, term(&d, &int(expected)))]
            ),
            Ok(Ok(Validity::Valid))
        );
        let domain = Predicate::Ceil(term(
            &d,
            &format!("choose{{}}({},{},{})", boolv(true), int(6), int(0)),
        ));
        let domain = if defined_at_zero {
            domain
        } else {
            Predicate::Not(Arc::new(domain))
        };
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &[domain]),
            Ok(Ok(Validity::Valid))
        );
        let strict_domain = Predicate::Ceil(term(
            &d,
            &format!("strictChoose{{}}({},{},{})", boolv(false), int(6), int(0)),
        ));
        let strict_domain = if defined_at_zero {
            strict_domain
        } else {
            Predicate::Not(Arc::new(strict_domain))
        };
        assert_eq!(
            solver.check_predicates(&[], &Substitution::new(), &[strict_domain]),
            Ok(Ok(Validity::Valid))
        );
        let strict_domain = Predicate::Ceil(term(
            &d,
            &format!(
                "strictChoose{{}}({}, {}, SYM:SortInt{{}})",
                boolv(false),
                int(6)
            ),
        ));
        let strict_domain = if defined_at_zero {
            strict_domain
        } else {
            Predicate::Not(Arc::new(strict_domain))
        };
        let known = [
            Predicate::Equals(term(&d, "SYM:SortInt{}"), term(&d, &int(0))),
            Predicate::Ceil(term(
                &d,
                &format!("ediv{{}}({},plus{{}}(SYM:SortInt{{}},{}) )", int(6), int(1)),
            )),
        ];
        assert_eq!(
            solver.check_predicates(&known, &Substitution::new(), &[strict_domain]),
            Ok(Ok(Validity::Valid))
        );
    }
    let explicit = baseline.replace("endmodule []", "axiom{R} \\implies{R}(\\top{R}(),\\equals{R,R}(\\ceil{SortInt{},R}(choose{}(B:SortBool{},X:SortInt{},Y:SortInt{})),\\bottom{R}())) []\nendmodule []");
    let d = BackendDefinition::internalize(&parse_definition(&explicit).unwrap(), "MAIN").unwrap();
    assert_eq!(
        Catalog::new(&d)
            .admit(&term(&d, "choose{}(B:SortBool{},X:SortInt{},Y:SortInt{})"))
            .unwrap(),
        Err(Rejected::Unsupported)
    );
}

#[test]
fn an_admitted_partial_body_cannot_make_the_same_expression_a_total_partition_test() {
    let quotient = format!("ediv{{}}({},X:SortInt{{}})", int(1));
    let guard = format!("lt{{}}({},{quotient})", int(0));
    let rows = [
        equation("magnitude{}(X:SortInt{})", &quotient, Some(&guard), ""),
        equation(
            "magnitude{}(X:SortInt{})",
            &int(0),
            Some(&format!("not{{}}({guard})")),
            "",
        ),
    ]
    .join("\n");
    let source = partial_source().replace("endmodule []", &format!("{rows}\nendmodule []"));
    let d = BackendDefinition::internalize(&parse_definition(&source).unwrap(), "MAIN").unwrap();
    assert!(
        Catalog::new(&d)
            .admit(&term(&d, "magnitude{}(X:SortInt{})"))
            .unwrap()
            .is_err()
    );
}

#[cfg(feature = "z3")]
#[test]
fn a_source_decided_nullary_partial_domain_needs_no_empty_boolean_application() {
    use crate::{
        smt::{SmtSolver, Validity, Z3Solver},
        substitution::Substitution,
    };
    let d = definition(
        r#"
      symbol zero{}() : SortInt{} [function{}()]
      axiom{R} \implies{R}(\top{R}(),\equals{R,R}(\ceil{SortInt{},R}(zero{}()),\bottom{R}())) []
    "#,
    );
    assert_eq!(
        Z3Solver::new(&d).unwrap().check_predicates(
            &[],
            &Substitution::new(),
            &[Predicate::Not(Arc::new(Predicate::Ceil(term(
                &d, "zero{}()"
            ))))]
        ),
        Ok(Ok(Validity::Valid))
    );
}

#[cfg(feature = "z3")]
#[test]
fn a_globally_defined_partial_helper_can_supply_a_total_partition_test() {
    use crate::{
        smt::{SmtSolver, Validity, Z3Solver},
        substitution::Substitution,
    };
    let mut rows = vec!["symbol testBit{}(SortBool{}) : SortBool{} [function{}()]".to_owned()];
    for b in [false, true] {
        rows.push(
            equation(&format!("testBit{{}}({})", boolv(b)), &boolv(b), None, "")
                .replace("\\equals{SortInt{},R}", "\\equals{SortBool{},R}")
                .replace("\\and{SortInt{}}", "\\and{SortBool{}}")
                .replace("\\top{SortInt{}}", "\\top{SortBool{}}"),
        );
    }
    let guard = format!("testBit{{}}(ge{{}}(X:SortInt{{}},{}) )", int(0));
    rows.push(equation(
        "magnitude{}(X:SortInt{})",
        &int(7),
        Some(&guard),
        "",
    ));
    rows.push(equation(
        "magnitude{}(X:SortInt{})",
        &int(9),
        Some(&format!("not{{}}({guard})")),
        "",
    ));
    let rows = rows.join("\n");
    let raw_equal = format!(
        r"\equals{{SortBool{{}},R}}({guard},testBit{{}}({}))",
        boolv(true)
    );
    let raw = rows
        .replace(
            &format!(r"\equals{{SortBool{{}},R}}({guard},{})", boolv(true)),
            &raw_equal,
        )
        .replace(
            &format!(
                r"\equals{{SortBool{{}},R}}(not{{}}({guard}),{})",
                boolv(true)
            ),
            &format!(r"\not{{R}}({raw_equal})"),
        );
    for source in [rows, raw] {
        let d = definition(&source);
        let summary = Catalog::new(&d)
            .admit(&term(&d, "magnitude{}(X:SortInt{})"))
            .unwrap()
            .unwrap();
        assert!(summary.domain_total);
        let solver = Z3Solver::new(&d).unwrap();
        for (x, result) in [(-1, 9), (0, 7), (1, 7)] {
            assert_eq!(
                solver.check_predicates(
                    &[],
                    &Substitution::new(),
                    &[Predicate::Equals(
                        term(&d, &format!("magnitude{{}}({})", int(x))),
                        term(&d, &int(result))
                    )]
                ),
                Ok(Ok(Validity::Valid))
            );
        }
    }
}

#[cfg(feature = "z3")]
#[test]
fn a_partial_boolean_summary_keeps_false_values_distinct_from_false_domains() {
    use crate::{
        smt::{SmtSolver, Validity, Z3Solver},
        substitution::Substitution,
    };
    let d = BackendDefinition::internalize(&parse_definition(&partial_source()).unwrap(), "MAIN")
        .unwrap();
    let solver = Z3Solver::new(&d).unwrap();
    let defined_false = term(
        &d,
        &format!("chooseBool{{}}({},{},{})", boolv(false), int(6), int(0)),
    );
    assert_eq!(
        solver.check_predicates(
            &[],
            &Substitution::new(),
            &[
                Predicate::Ceil(defined_false.clone()),
                Predicate::Not(Arc::new(Predicate::Term(defined_false)))
            ]
        ),
        Ok(Ok(Validity::Valid))
    );
    let undefined = term(
        &d,
        &format!("chooseBool{{}}({},{},{})", boolv(true), int(6), int(0)),
    );
    assert_eq!(
        solver.check_predicates(
            &[],
            &Substitution::new(),
            &[Predicate::Not(Arc::new(Predicate::Ceil(undefined)))]
        ),
        Ok(Ok(Validity::Valid))
    );
}
