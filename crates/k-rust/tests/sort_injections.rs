use std::sync::Arc;

use indoc::indoc;
use k_rust::definition::{
    Attributes, Definition, FlatImport, FlatModule, LOCATION_ATTRIBUTE, ProductionItem,
    ResolvedDefinition, SOURCE_ATTRIBUTE, Sentence,
};
use k_rust::inner::resolve_rule_bubbles;
use k_rust::kast::{Label, ProductionIdentity, Sort, Term, TermMetadata};
use k_rust::kompile::{
    SortInjectionError, SortInjector, add_sort_injections_to_definition, generate_sort_projections,
    term_to_kore_from_resolved,
};
use k_rust::kore::printer::Printer;
use k_rust::provenance::{GeneratingPass, ORIGIN_ATTRIBUTE};
use serde_json::json;

fn lowered(source: &str) -> Definition {
    let parsed = k_rust::outer::parse("injections.k", source).expect("definition should parse");
    let definition = k_rust::outer::lower(&parsed, "MAIN").expect("definition should lower");
    resolve_rule_bubbles(&definition).expect("rule bubbles should resolve")
}

#[derive(Debug)]
#[allow(dead_code)]
struct InjectionSummary {
    injected: String,
    kore: String,
}

macro_rules! injection_snapshot {
    ($name:ident, $source:expr) => {
        #[test]
        fn $name() {
            let source = indoc!($source);
            let definition = generate_sort_projections(&lowered(source))
                .expect("sort projections should generate");
            let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
            let injector = SortInjector::new(&resolved, "MAIN").expect("injector should build");
            let summaries = definition
                .main_module()
                .expect("main module should exist")
                .local_sentences
                .iter()
                .filter(|sentence| {
                    matches!(&***sentence, Sentence::Rule { .. } | Sentence::Claim { .. })
                        && sentence.attributes().get("projection").is_none()
                })
                .map(|sentence| {
                    let injected = injector
                        .inject_sentence(sentence)
                        .expect("sort injections should succeed");
                    let body = match &injected {
                        Sentence::Rule { body, .. } | Sentence::Claim { body, .. } => body,
                        _ => unreachable!(),
                    };
                    let kore = term_to_kore_from_resolved(&resolved, "MAIN", body)
                        .expect("injected term should convert to KORE");
                    InjectionSummary {
                        injected: body.to_string(),
                        kore: Printer::pretty(100).print_pattern(&kore),
                    }
                })
                .collect::<Vec<_>>();
            insta::with_settings!({
                description => format!("K definition:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(summaries);
            });
        }
    };
}

#[test]
fn reference_constructor_arguments_inject_only_a_strict_subsort() {
    // reference: kast --definition ref --module MAIN --sort Box --output kore -e 'box(small)'
    let definition = lowered(include_str!(
        "fixtures/reference/injections/arguments/test.k"
    ));
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    for (argument, expected) in [
        (
            "small",
            include_str!("fixtures/reference/injections/arguments/subsort.kore"),
        ),
        (
            "large",
            include_str!("fixtures/reference/injections/arguments/exact-sort.kore"),
        ),
    ] {
        let term = Term::apply("box", vec![Term::apply(argument, vec![])]);
        let injected = injector.inject_at_top(&term).unwrap();
        let actual = term_to_kore_from_resolved(&resolved, "MAIN", &injected).unwrap();
        let expected = k_rust::kore::parser::parse_pattern(expected).unwrap();
        assert_eq!(actual, expected, "argument {argument}");
    }
}

#[test]
fn recovers_a_stale_catalog_identity_for_a_unique_label() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let module = resolved.module_id("MAIN").unwrap();
    let catalog = resolved.production_catalog(module);
    let stale = catalog.productions_for(&k_rust::definition::LabelHead::new("b"))[0];
    let term = Term::apply("a", Vec::new()).with_metadata(TermMetadata {
        span: None,
        production: Some(ProductionIdentity::from_hex(&format!("{:032x}", stale.0)).unwrap()),
        sort: None,
        origin: None,
    });
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();

    assert_eq!(
        injector.inject_at_top(&term).unwrap().to_string(),
        "a(.KList)"
    );
}

#[test]
fn stale_catalog_identity_uses_metadata_sort_to_disambiguate_a_label() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(choice)]
          syntax B ::= "b" [symbol(choice)]
          syntax Stale ::= "stale" [symbol(stale)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let module = resolved.module_id("MAIN").unwrap();
    let catalog = resolved.production_catalog(module);
    let stale = catalog.productions_for(&k_rust::definition::LabelHead::new("stale"))[0];
    let term = Term::apply("choice", Vec::new()).with_metadata(TermMetadata {
        span: None,
        production: Some(ProductionIdentity::from_hex(&format!("{:032x}", stale.0)).unwrap()),
        sort: Some(Sort::new("A")),
        origin: None,
    });
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();

    assert_eq!(
        injector.inject_at_top(&term).unwrap().to_string(),
        "choice(.KList)"
    );
}

#[test]
fn config_dependent_sort_predicate_has_the_reference_error() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Bool
          syntax Exp
          syntax Bool ::= isExp(Exp) [function, symbol(isExp)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let term = Term::apply(
        "isExp",
        vec![Term::variable("X"), Term::variable("THIS_CONFIGURATION")],
    );
    let error = injector
        .inject_at_top(&term)
        .expect_err("configuration-dependent predicates must be rejected");
    assert_eq!(
        error.to_string(),
        "Invalid sort predicate isExp that depends directly or indirectly on the current configuration. Is it possible to replace the sort predicate with a regular function?"
    );
}

#[test]
fn reconstructs_a_singleton_user_list_for_generated_terms() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Item ::= "item" [symbol(item)]
          syntax Items ::= List{Item, ""} [symbol(items), terminator-symbol(.Items)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let item = Term::Variable {
        name: "X".into(),
        sort: Some(Sort::new("Item")),
    };

    let injected = injector.inject(&item, &Sort::new("Items")).unwrap();

    assert_eq!(injected.to_string(), "items(X,`.Items`(.KList))");
}

injection_snapshot!(
    inserts_subsort_injections_in_production_arguments,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Stmt ::= "print" Exp [symbol(print)]

          rule print 1 => print 2
        endmodule
    "#
);

#[cfg(feature = "z3-inference")]
#[test]
fn semantic_casts_instantiate_parametric_production_results() {
    let source = indoc! {r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax C ::= A | B
          syntax D ::= A | B
          syntax {S} S ::= "pair(" S "," S ")" [symbol(pair)]

          rule pair(a, b):C => pair(a, b):C
        endmodule
    "#};
    let definition = k_rust::kompile::resolve_semantic_casts(&lowered(source)).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let rule = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| matches!(&***sentence, Sentence::Rule { .. }))
        .unwrap();
    let injected = injector.inject_sentence(rule).unwrap();
    let Sentence::Rule { body, .. } = injected else {
        unreachable!()
    };
    let rendered = body.to_string();

    assert_eq!(rendered.matches("pair{C}").count(), 2, "{rendered}");
    assert_eq!(rendered.matches("inj{A,C}").count(), 2, "{rendered}");
    assert_eq!(rendered.matches("inj{B,C}").count(), 2, "{rendered}");
}

// `use(X:Value)` with `MInt{8} < Value` has no instantiation of `W` under which `Value <= MInt{W}`:
// the only declared instance, `MInt{8}`, lies below `Value`. `inj{Value, MInt{8}}` would not embed
// `Value` in `MInt{8}` (the definition declares no such subsort), so the term is ill-sorted and the
// injector rejects it instead of building that injection.
#[test]
fn parametric_argument_above_every_declared_instance_is_rejected() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax MInt{8}
          syntax Value ::= MInt{8}
          syntax Result
          syntax {W} Result ::= "use(" MInt{W} ")" [symbol(use)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let term = Term::apply(
        "use",
        vec![Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new("Value")),
        }],
    );

    let error = injector.inject(&term, &Sort::new("Result")).unwrap_err();

    assert!(
        matches!(
            &error,
            // No instance of `MInt{W}` lies at or above `Value`, so `W` stays a sort variable and
            // no declared instance of `MInt{W}` admits the argument.
            SortInjectionError::IllSortedTerm(mismatch)
                if mismatch.found == Sort::new("Value") && mismatch.required.name == "MInt"
        ),
        "{error}"
    );
}

// An argument whose sort is declared below `MInt{8}` fits `MInt{W}` at `W = 8`: the instance is
// found above the argument's sort and the argument is injected upward into it.
#[test]
fn parametric_argument_below_a_declared_instance_instantiates_it() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax MInt{8}
          syntax Byte
          syntax MInt{8} ::= Byte
          syntax Result
          syntax {W} Result ::= "use(" MInt{W} ")" [symbol(use)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let term = Term::apply(
        "use",
        vec![Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new("Byte")),
        }],
    );

    let injected = injector.inject(&term, &Sort::new("Result")).unwrap();
    let Term::Apply { label, arguments } = injected.unannotated() else {
        panic!("expected the parametric use application");
    };

    assert_eq!(label.parameters, vec![Sort::new("8")]);
    assert!(
        matches!(
            arguments.as_slice(),
            [Term::Apply { label, .. }]
                if label.name == "inj"
                    && label.parameters == vec![Sort::new("Byte"), Sort::with_parameters("MInt", vec![Sort::new("8")])]
        ),
        "{injected}"
    );
}

fn use_injector(source: &str) -> (Definition, ResolvedDefinition) {
    let definition = lowered(source);
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    (definition, resolved)
}

fn use_of(sort: Sort) -> Term {
    Term::apply(
        "use",
        vec![Term::Variable {
            name: "X".into(),
            sort: Some(sort),
        }],
    )
}

fn mint(width: &str) -> Sort {
    Sort::with_parameters("MInt", vec![Sort::new(width)])
}

// An argument that is itself an instance of `MInt{W}` fixes `W` exactly, even when a larger
// declared instance lies above it: `MInt{8}` needs no injection and gives `use{8}`.
#[test]
fn parametric_argument_that_is_an_instance_binds_it_exactly() {
    let (_, resolved) = use_injector(indoc! {r#"
        module MAIN
          syntax MInt{8}
          syntax MInt{16}
          syntax MInt{16} ::= MInt{8}
          syntax Result
          syntax {W} Result ::= "use(" MInt{W} ")" [symbol(use)]
        endmodule
    "#});
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();

    let injected = injector
        .inject(&use_of(mint("8")), &Sort::new("Result"))
        .unwrap();
    let Term::Apply { label, arguments } = injected.unannotated() else {
        panic!("expected the parametric use application");
    };

    assert_eq!(label.parameters, vec![Sort::new("8")], "{injected}");
    assert!(
        matches!(arguments.as_slice(), [Term::Variable { .. }]),
        "{injected}"
    );
}

// The least instance above the argument is chosen, not an upper bound of every instance above it:
// with `Byte < MInt{8} < MInt{16}`, `use(X:Byte)` is `use{8}` with `inj{Byte, MInt{8}}`.
#[test]
fn parametric_argument_instantiates_the_least_instance_above_it() {
    let (_, resolved) = use_injector(indoc! {r#"
        module MAIN
          syntax MInt{8}
          syntax MInt{16}
          syntax Byte
          syntax MInt{8} ::= Byte
          syntax MInt{16} ::= MInt{8}
          syntax Result
          syntax {W} Result ::= "use(" MInt{W} ")" [symbol(use)]
        endmodule
    "#});
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();

    let injected = injector
        .inject(&use_of(Sort::new("Byte")), &Sort::new("Result"))
        .unwrap();
    let Term::Apply { label, arguments } = injected.unannotated() else {
        panic!("expected the parametric use application");
    };

    assert_eq!(label.parameters, vec![Sort::new("8")], "{injected}");
    assert!(
        matches!(
            arguments.as_slice(),
            [Term::Apply { label, .. }]
                if label.name == "inj" && label.parameters == vec![Sort::new("Byte"), mint("8")]
        ),
        "{injected}"
    );
}

// `Byte` lies below both `MInt{8}` and `MInt{16}`, which are incomparable: no instance fits it most
// tightly, so the instantiation is ambiguous rather than an upper bound of `8` and `16`.
#[test]
fn parametric_argument_with_incomparable_least_instances_is_ambiguous() {
    let (_, resolved) = use_injector(indoc! {r#"
        module MAIN
          syntax MInt{8}
          syntax MInt{16}
          syntax Byte
          syntax MInt{8} ::= Byte
          syntax MInt{16} ::= Byte
          syntax Result
          syntax {W} Result ::= "use(" MInt{W} ")" [symbol(use)]
        endmodule
    "#});
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();

    let error = injector
        .inject(&use_of(Sort::new("Byte")), &Sort::new("Result"))
        .unwrap_err();

    assert!(
        matches!(
            &error,
            SortInjectionError::AmbiguousInstance(ambiguity)
                if ambiguity.arguments == vec![Sort::new("Byte")]
                    && ambiguity.candidates == vec![vec![mint("16")], vec![mint("8")]]
        ),
        "{error}"
    );
}

const TWO_WIDTHS: &str = indoc! {r#"
    module MAIN
      syntax MInt{8}
      syntax MInt{16}
      syntax Byte
      syntax MInt{8} ::= Byte
      syntax MInt{16} ::= Byte
      syntax MInt{16} ::= MInt{8}
      syntax Result
      syntax {W} Result ::= "use2(" MInt{W} "," MInt{W} ")" [symbol(use2)]
    endmodule
"#};

fn use2_of(left: Sort, right: Sort) -> Term {
    Term::apply(
        "use2",
        vec![
            Term::Variable {
                name: "X".into(),
                sort: Some(left),
            },
            Term::Variable {
                name: "Y".into(),
                sort: Some(right),
            },
        ],
    )
}

fn injected_use2(left: Sort, right: Sort) -> Result<Term, SortInjectionError> {
    let (_, resolved) = use_injector(TWO_WIDTHS);
    SortInjector::new(&resolved, "MAIN")
        .unwrap()
        .inject(&use2_of(left, right), &Sort::new("Result"))
}

// One parameter shared by two arguments is instantiated for both at once: `use2(X:MInt{8},
// Y:MInt{16})` is well sorted at `W = 16`, where the first argument is injected upward.
#[test]
fn shared_parameter_is_instantiated_jointly_over_the_arguments() {
    let injected = injected_use2(mint("8"), mint("16")).unwrap();
    let Term::Apply { label, arguments } = injected.unannotated() else {
        panic!("expected the parametric use2 application");
    };

    assert_eq!(label.parameters, vec![Sort::new("16")], "{injected}");
    assert!(
        matches!(
            arguments.as_slice(),
            [Term::Apply { label, .. }, Term::Variable { .. }]
                if label.name == "inj" && label.parameters == vec![mint("8"), mint("16")]
        ),
        "{injected}"
    );
}

// Alone, `Byte` would take its least instance `MInt{8}`; a second argument of sort `MInt{16}` rules
// out `W = 8`, so the joint instantiation is `W = 16` for both arguments.
#[test]
fn later_argument_selects_the_instance_for_an_earlier_one() {
    let injected = injected_use2(Sort::new("Byte"), mint("16")).unwrap();
    let Term::Apply { label, .. } = injected.unannotated() else {
        panic!("expected the parametric use2 application");
    };

    assert_eq!(label.parameters, vec![Sort::new("16")], "{injected}");
}

// Without `MInt{8} < MInt{16}`, `Byte` has two incomparable least instances; a second argument of
// sort `MInt{8}` resolves the choice, while two `Byte` arguments leave it ambiguous.
#[test]
fn joint_ambiguity_is_resolved_by_another_argument_or_reported() {
    let source = TWO_WIDTHS.replace("  syntax MInt{16} ::= MInt{8}\n", "");
    assert_ne!(source, TWO_WIDTHS);
    let (_, resolved) = use_injector(&source);
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();

    let resolved_by_second = injector
        .inject(&use2_of(Sort::new("Byte"), mint("8")), &Sort::new("Result"))
        .unwrap();
    let Term::Apply { label, .. } = resolved_by_second.unannotated() else {
        panic!("expected the parametric use2 application");
    };
    assert_eq!(
        label.parameters,
        vec![Sort::new("8")],
        "{resolved_by_second}"
    );

    let error = injector
        .inject(
            &use2_of(Sort::new("Byte"), Sort::new("Byte")),
            &Sort::new("Result"),
        )
        .unwrap_err();
    assert!(
        matches!(
            &error,
            SortInjectionError::AmbiguousInstance(ambiguity)
                if ambiguity.candidates
                    == vec![vec![mint("16"), mint("16")], vec![mint("8"), mint("8")]]
        ),
        "{error}"
    );
}

// The exact assignment is only a first try: `make(X:MInt{8})` at an `R{16}` position would be
// `W = 8` exactly, but `R{8}` does not fit the position, while `W = 16` fits both the argument
// (through `MInt{8} < MInt{16}`) and the position.
#[test]
fn position_constraint_overrides_the_exact_argument_instance() {
    let (_, resolved) = use_injector(indoc! {r#"
        module MAIN
          syntax MInt{8}
          syntax MInt{16}
          syntax MInt{16} ::= MInt{8}
          syntax R{8}
          syntax R{16}
          syntax {W} R{W} ::= "make(" MInt{W} ")" [symbol(make)]
        endmodule
    "#});
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let term = Term::apply(
        "make",
        vec![Term::Variable {
            name: "X".into(),
            sort: Some(mint("8")),
        }],
    );

    let injected = injector
        .inject(&term, &Sort::with_parameters("R", vec![Sort::new("16")]))
        .unwrap();
    let Term::Apply { label, arguments } = injected.unannotated() else {
        panic!("expected the parametric make application");
    };

    assert_eq!(label.parameters, vec![Sort::new("16")], "{injected}");
    assert!(
        matches!(
            arguments.as_slice(),
            [Term::Apply { label, .. }]
                if label.name == "inj" && label.parameters == vec![mint("8"), mint("16")]
        ),
        "{injected}"
    );
}

// All parameters are solved together: `Byte` alone fits `Pair{W, T}` at two incomparable
// instances, but `Box{W}` at `Box{A}` fixes `W = A` and the whole-sort argument fixes `T = Int`.
#[test]
fn whole_and_nested_parameters_are_solved_together() {
    let (_, resolved) = use_injector(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax Int
          syntax Byte
          syntax Pair{A, Int}
          syntax Pair{B, Int}
          syntax Pair{A, Int} ::= Byte
          syntax Pair{B, Int} ::= Byte
          syntax Box{A}
          syntax Box{B}
          syntax Result
          syntax {W, T} Result ::= "f(" Pair{W, T} "," Box{W} "," T ")" [symbol(f)]
        endmodule
    "#});
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let variable = |name: &str, sort: Sort| Term::Variable {
        name: name.into(),
        sort: Some(sort),
    };
    let pair_a_int = Sort::with_parameters("Pair", vec![Sort::new("A"), Sort::new("Int")]);
    let term = Term::apply(
        "f",
        vec![
            variable("X", Sort::new("Byte")),
            variable("Y", Sort::with_parameters("Box", vec![Sort::new("A")])),
            variable("Z", Sort::new("Int")),
        ],
    );

    let injected = injector.inject(&term, &Sort::new("Result")).unwrap();
    let Term::Apply { label, arguments } = injected.unannotated() else {
        panic!("expected the parametric f application");
    };

    assert_eq!(
        label.parameters,
        vec![Sort::new("A"), Sort::new("Int")],
        "{injected}"
    );
    assert!(
        matches!(
            arguments.as_slice(),
            [Term::Apply { label, .. }, Term::Variable { .. }, Term::Variable { .. }]
                if label.name == "inj" && label.parameters == vec![Sort::new("Byte"), pair_a_int.clone()]
        ),
        "{injected}"
    );
}

fn nat_as_definition() -> ResolvedDefinition {
    ResolvedDefinition::resolve(&lowered(indoc! {r#"
        module MAIN
          syntax Nat ::= "z" [symbol(z)]
          syntax Bool ::= "t" [symbol(t)]
        endmodule
    "#}))
    .unwrap()
}

fn as_pattern(alias_sort: Option<&str>) -> Term {
    Term::As {
        pattern: Box::new(Term::apply("z", vec![])),
        alias: Box::new(Term::Variable {
            name: "X".into(),
            sort: alias_sort.map(Sort::new),
        }),
    }
    .with_metadata(TermMetadata {
        sort: Some(Sort::new("Nat")),
        ..TermMetadata::default()
    })
}

// The alias of `(z #as X):Nat` names a `Nat`: a sortless `X` takes that sort, `X:Nat` is kept, and
// `X:Bool` is rejected instead of being retyped to `Nat`.
#[test]
fn sorted_alias_of_a_cast_as_pattern_must_fit_the_cast() {
    let resolved = nat_as_definition();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let alias_sort = |injected: &Term| match injected.unannotated() {
        Term::As { alias, .. } => match alias.unannotated() {
            Term::Variable { sort, .. } => sort.clone(),
            other => panic!("alias is not a variable: {other}"),
        },
        other => panic!("expected an as-pattern: {other}"),
    };

    for alias in [None, Some("Nat")] {
        let injected = injector
            .inject(&as_pattern(alias), &Sort::new("Nat"))
            .unwrap();
        assert_eq!(alias_sort(&injected), Some(Sort::new("Nat")), "{injected}");
    }
    let error = injector
        .inject(&as_pattern(Some("Bool")), &Sort::new("Nat"))
        .unwrap_err();
    assert!(
        matches!(&error, SortInjectionError::IllSortedTerm(mismatch)
            if mismatch.found == Sort::new("Bool") && mismatch.required == Sort::new("Nat")),
        "{error}"
    );
}

fn sort_variable(name: &str) -> Sort {
    Sort::with_parameters("#SortParam", vec![Sort::new(name)])
}

fn sorted_variable(sort: Sort) -> Term {
    Term::Variable {
        name: "X".into(),
        sort: Some(sort),
    }
}

// A sort parameter is universally quantified, so `MInt{Q} <= MInt{8}` would have to hold for every
// `Q`; that `Q = 8` is one witness does not justify `inj{MInt{Q}, MInt{8}}`. `MInt{Q}` stands
// below `KItem` for every `Q` (its head is not a parser sort) and below itself.
#[test]
fn sort_with_a_sort_variable_is_below_only_what_every_instance_is_below() {
    let (_, resolved) = use_injector(indoc! {r#"
        module MAIN
          syntax MInt{8}
        endmodule
    "#});
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let parametric = Sort::with_parameters("MInt", vec![sort_variable("Q")]);

    let error = injector
        .inject(&sorted_variable(parametric.clone()), &mint("8"))
        .unwrap_err();
    assert!(
        matches!(&error, SortInjectionError::IllSortedTerm(mismatch)
            if mismatch.found == parametric && mismatch.required == mint("8")),
        "{error}"
    );
    let bare = injector
        .inject(&sorted_variable(sort_variable("Q")), &mint("8"))
        .unwrap_err();
    assert!(
        matches!(bare, SortInjectionError::IllSortedTerm(_)),
        "{bare}"
    );

    injector
        .inject(&sorted_variable(parametric.clone()), &parametric)
        .unwrap();
    let to_kitem = injector
        .inject(&sorted_variable(parametric.clone()), &Sort::new("KItem"))
        .unwrap();
    assert!(
        matches!(to_kitem.unannotated(), Term::Apply { label, .. }
            if label.name == "inj" && label.parameters == vec![parametric.clone(), Sort::new("KItem")]),
        "{to_kitem}"
    );
}

// One sort variable occurring twice stands for one sort: `Pair{Q, Q}` has no instance
// `Pair{A, B}` with `A` and `B` distinct, and `Pair{Q, Q}` and `Pair{Q, R}` are different sorts.
#[test]
fn repeated_sort_variable_is_one_sort() {
    let (_, resolved) = use_injector(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax Pair{A, B}
        endmodule
    "#});
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let pair = |left: Sort, right: Sort| Sort::with_parameters("Pair", vec![left, right]);
    let diagonal = pair(sort_variable("Q"), sort_variable("Q"));

    for expected in [
        pair(Sort::new("A"), Sort::new("B")),
        pair(sort_variable("Q"), sort_variable("R")),
    ] {
        let error = injector
            .inject(&sorted_variable(diagonal.clone()), &expected)
            .unwrap_err();
        assert!(
            matches!(error, SortInjectionError::IllSortedTerm(_)),
            "{expected}: {error}"
        );
    }
    injector
        .inject(&sorted_variable(diagonal.clone()), &diagonal)
        .unwrap();
}

fn cast_to(sort: &str, term: Term) -> Term {
    term.with_metadata(TermMetadata {
        sort: Some(Sort::new(sort)),
        ..TermMetadata::default()
    })
}

fn sequence_definition() -> (Definition, ResolvedDefinition) {
    let definition = generate_sort_projections(&lowered(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax KItem ::= Int
          syntax K ::= KItem
        endmodule
    "#}))
    .expect("sort projections should generate");
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    (definition, resolved)
}

// A cast on a K sequence compares the target with the sequence's own sort `K` like any other
// operand: `Int < K` is a downcast, realized by `project:Int`.
#[test]
fn cast_of_a_k_sequence_below_k_is_a_projected_downcast() {
    let (_, resolved) = sequence_definition();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let sequence = cast_to(
        "Int",
        Term::Sequence(vec![Term::Token {
            token: "1".into(),
            sort: Sort::new("Int"),
        }]),
    );

    let injected = injector.inject(&sequence, &Sort::new("Int")).unwrap();

    assert!(
        matches!(injected.unannotated(), Term::Apply { label, arguments }
            if label.name == "project:Int" && matches!(arguments.as_slice(), [argument]
                if matches!(argument.unannotated(), Term::Sequence(_)))),
        "{injected}"
    );
}

// `KConfigVar` is neither above nor below `K` here, so a K sequence cast to it is rejected.
#[test]
fn cast_of_a_k_sequence_to_an_incomparable_sort_is_rejected() {
    let (_, resolved) = sequence_definition();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let sequence = cast_to("KConfigVar", Term::Sequence(Vec::new()));

    let error = injector
        .inject(&sequence, &Sort::new("KConfigVar"))
        .unwrap_err();

    assert!(
        matches!(&error, SortInjectionError::IncomparableCast(mismatch)
            if mismatch.found == Sort::new("K") && mismatch.required == Sort::new("KConfigVar")),
        "{error}"
    );
}

fn wem10_bound_definition(source: &str) -> ResolvedDefinition {
    ResolvedDefinition::resolve(&lowered(source)).unwrap()
}

fn wem10_bound_injector() -> ResolvedDefinition {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax MInt{8}
          syntax KItem ::= MInt{8}
          syntax K
          syntax K ::= KItem
          syntax KBott
          syntax KItem ::= KBott
          syntax KList
          syntax KList ::= K
        endmodule
    "#});
    ResolvedDefinition::resolve(&definition).unwrap()
}

fn rewrite_tokens(left: Sort, right: Sort) -> Term {
    Term::Rewrite {
        left: Box::new(Term::Token {
            token: "left".into(),
            sort: left,
        }),
        right: Box::new(Term::Token {
            token: "right".into(),
            sort: right,
        }),
    }
}

#[test]
fn wem10_bound_resolves_unfixed_parametric_entry_through_declared_instantiations() {
    let definition = wem10_bound_injector();
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let unresolved = Sort::with_parameters(
        "MInt",
        vec![Sort::with_parameters("#SortParam", vec![Sort::new("Q")])],
    );
    let rewrite = rewrite_tokens(unresolved.clone(), unresolved);

    assert_eq!(
        injector.term_sort(&rewrite, None).unwrap(),
        Sort::with_parameters("MInt", vec![Sort::new("8")])
    );
}

#[test]
fn wem10_bound_filters_concrete_seed_bounds_through_declared_instantiations() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax Int
          syntax Bool
          syntax Box{Int}
          syntax Box{Bool}
          syntax Seed
          syntax Good ::= Seed
          syntax Good ::= Box{Int}
          syntax Decoy ::= Seed
          syntax K ::= Good
          syntax K ::= Decoy
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let unresolved = Sort::with_parameters(
        "Box",
        vec![Sort::with_parameters("#SortParam", vec![Sort::new("Q")])],
    );
    let rewrite = rewrite_tokens(unresolved, Sort::new("Seed"));

    assert_eq!(
        injector.term_sort(&rewrite, None).unwrap(),
        Sort::new("Good")
    );
}

#[test]
fn wem10_bound_excludes_kbott_and_lower_parser_sorts() {
    let definition = wem10_bound_injector();
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("KBott"), Sort::new("KBott"));

    assert_eq!(
        injector.term_sort(&rewrite, None).unwrap(),
        Sort::new("KItem")
    );
}

#[test]
fn wem10_bound_excludes_a_strict_lower_parser_sort() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax ParserLow ::= A
          syntax ParserLow ::= B
          syntax KBott ::= ParserLow
          syntax KItem ::= KBott
          syntax K ::= KItem
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert_eq!(
        injector.term_sort(&rewrite, None).unwrap(),
        Sort::new("KItem")
    );
}

#[test]
fn wem10_bound_rejects_sorts_above_k() {
    let definition = wem10_bound_injector();
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("KList"), Sort::new("KList"));

    assert!(matches!(
        injector.term_sort(&rewrite, None),
        Err(SortInjectionError::IncompatibleSorts { .. })
    ));
}

#[test]
fn wem10_bound_rejects_a_distinct_common_bound_above_k() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax K
          syntax Above ::= A
          syntax Above ::= B
          syntax Above ::= K
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert!(matches!(
        injector.term_sort(&rewrite, None),
        Err(SortInjectionError::IncompatibleSorts { .. })
    ));
}

#[test]
fn wem10_bound_retains_a_relation_free_singleton() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("A"));

    assert_eq!(injector.term_sort(&rewrite, None).unwrap(), Sort::new("A"));
}

#[test]
fn wem10_bound_retains_a_unique_semantic_bound() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax C ::= A
          syntax C ::= B
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert_eq!(injector.term_sort(&rewrite, None).unwrap(), Sort::new("C"));
}

#[test]
fn wem10_bound_rejects_ambiguous_minima() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax C ::= A
          syntax C ::= B
          syntax D ::= A
          syntax D ::= B
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert!(matches!(
        injector.term_sort(&rewrite, None),
        Err(SortInjectionError::IncompatibleSorts { .. })
    ));
}

#[test]
fn wem10_bound_rejects_absent_common_bound() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert!(matches!(
        injector.term_sort(&rewrite, None),
        Err(SortInjectionError::IncompatibleSorts { .. })
    ));
}

#[test]
fn wem10_bound_preserves_the_expected_sort_ceiling() {
    let definition = wem10_bound_definition(indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax C ::= A
          syntax C ::= B
          syntax D ::= C
        endmodule
    "#});
    let injector = SortInjector::new(&definition, "MAIN").unwrap();
    let rewrite = rewrite_tokens(Sort::new("A"), Sort::new("B"));

    assert_eq!(
        injector.term_sort(&rewrite, Some(&Sort::new("D"))).unwrap(),
        Sort::new("C")
    );
    assert!(matches!(
        injector.term_sort(&rewrite, Some(&Sort::new("A"))),
        Err(SortInjectionError::IncompatibleSorts { .. })
    ));
}

#[test]
fn semantic_casts_project_heterogeneous_collection_results() {
    let mut definition = lowered(indoc! {r#"
        module MAIN
          syntax Bool ::= "true" [token]
          syntax Int ::= r"[0-9]+" [token]
          syntax List
          syntax Map
          syntax KItem ::= List "[" Int "]" [function, hook(LIST.get), symbol(List:get)]
          syntax KItem ::= Map "[" Int "]" [function, hook(MAP.lookup), symbol(Map:lookup)]
        endmodule
    "#});
    let truth = || Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let get = |label: &str, collection_sort: &str| {
        Term::apply(
            "#SemanticCastToInt",
            vec![Term::apply(
                label,
                vec![
                    Term::Variable {
                        name: "COLLECTION".into(),
                        sort: Some(Sort::new(collection_sort)),
                    },
                    Term::Token {
                        token: "0".into(),
                        sort: Sort::new("Int"),
                    },
                ],
            )],
        )
    };
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == definition.main_module)
        .unwrap();
    module.local_sentences.extend(
        [
            Sentence::Rule {
                body: get("List:get", "List"),
                requires: truth(),
                ensures: truth(),
                attributes: Attributes::default(),
            },
            Sentence::Rule {
                body: get("Map:lookup", "Map"),
                requires: truth(),
                ensures: truth(),
                attributes: Attributes::default(),
            },
        ]
        .into_iter()
        .map(std::sync::Arc::new),
    );

    let definition = k_rust::kompile::resolve_semantic_casts(&definition).unwrap();
    let definition = k_rust::kompile::subsort_kitem(&definition).unwrap();
    let definition = generate_sort_projections(&definition).unwrap();
    let definition = add_sort_injections_to_definition(&definition).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let summaries = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("projection").is_none() => Some((
                body.to_string(),
                Printer::pretty(100)
                    .print_pattern(&term_to_kore_from_resolved(&resolved, "MAIN", body).unwrap()),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::assert_debug_snapshot!(summaries, @r###"
    [
        (
            "`project:Int`(`List:get`(COLLECTION,#token(\"0\",\"Int\")))",
            "Lblproject'Coln'Int{}(\n  kseq{}(LblList'Coln'get{}(VarCOLLECTION:SortList{}, \\dv{SortInt{}}(\"0\")), dotk{}())\n)",
        ),
        (
            "`project:Int`(`Map:lookup`(COLLECTION,#token(\"0\",\"Int\")))",
            "Lblproject'Coln'Int{}(\n  kseq{}(LblMap'Coln'lookup{}(VarCOLLECTION:SortMap{}, \\dv{SortInt{}}(\"0\")), dotk{}())\n)",
        ),
    ]
    "###);
}

#[test]
fn a_semantic_downcast_application_sorts_as_the_projection_the_injector_builds() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax List
          syntax KItem ::= List "[" Int "]" [function, symbol(List:get)]
          syntax Int ::= "size" "(" List ")" [function, symbol(size)]
        endmodule
    "#});
    let definition = k_rust::kompile::subsort_kitem(&definition).unwrap();
    let definition = generate_sort_projections(&definition).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let list = || Term::Variable {
        name: "L".into(),
        sort: Some(Sort::new("List")),
    };
    let cast = |term: Term, sort: &str| {
        term.with_metadata(TermMetadata {
            sort: Some(Sort::new(sort)),
            ..TermMetadata::default()
        })
    };
    let get = || {
        Term::apply(
            "List:get",
            vec![
                list(),
                Term::Token {
                    token: "0".into(),
                    sort: Sort::new("Int"),
                },
            ],
        )
    };
    let downcast = cast(get(), "Int");
    let upcast = cast(Term::apply("size", vec![list()]), "KItem");
    let exact = cast(get(), "KItem");

    // (term, its sort, the term injected at that sort, the term injected at KItem)
    let cases = [
        (
            &downcast,
            "Int",
            "`project:Int`(`List:get`(L,#token(\"0\",\"Int\")))",
            "inj{Int,KItem}(`project:Int`(`List:get`(L,#token(\"0\",\"Int\"))))",
        ),
        (&upcast, "Int", "size(L)", "inj{Int,KItem}(size(L))"),
        (
            &exact,
            "KItem",
            "`List:get`(L,#token(\"0\",\"Int\"))",
            "`List:get`(L,#token(\"0\",\"Int\"))",
        ),
    ];
    for (term, sort, at_sort, at_kitem) in cases {
        let actual = injector.term_sort(term, None).unwrap();
        assert_eq!(actual, Sort::new(sort), "{term}");
        assert_eq!(injector.inject(term, &actual).unwrap().to_string(), at_sort);
        assert_eq!(
            injector
                .inject(term, &Sort::new("KItem"))
                .unwrap()
                .to_string(),
            at_kitem
        );
    }

    // A rewrite whose right side is the downcast sorts at the left side's Int, not KItem.
    let rewrite = Term::Rewrite {
        left: Box::new(Term::apply("size", vec![list()])),
        right: Box::new(downcast.clone()),
    };
    assert_eq!(
        injector.term_sort(&rewrite, None).unwrap(),
        Sort::new("Int")
    );
}

injection_snapshot!(
    injects_sequence_items_through_kitem,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]

          rule 1 ~> 2 => 2 ~> 1
        endmodule
    "#
);

#[cfg(feature = "z3-inference")]
injection_snapshot!(
    substitutes_parametric_production_signatures,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Box ::= "box(" Exp ")" [symbol(box)]
          syntax {S} S ::= "same(" S ")" [symbol(same)]

          rule box(same(1)) => box(1)
        endmodule
    "#
);

injection_snapshot!(
    preserves_semantic_cast_variable_context,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= Exp "+" Exp [symbol(_+_)]

          rule X:Exp + 0 => X:Exp
        endmodule
    "#
);

injection_snapshot!(
    injects_semantically_cast_tokens_from_their_intrinsic_sort,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]

          rule 1:KItem => 2:KItem
        endmodule
    "#
);

injection_snapshot!(
    handles_parser_generated_outer_casts,
    r#"
        module MAIN
          syntax Id ::= r"[a-z]" [token]
          syntax Exp ::= Id

          rule X:Exp => {X}:>Exp
        endmodule
    "#
);

injection_snapshot!(
    uses_resolved_overloaded_productions,
    r#"
        module MAIN
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax Result ::= "left" A [symbol(pick)]
                          | "right" B [symbol(pick)]
          syntax Value ::= A | B | Result
          syntax Wrapper ::= "wrap" Value [symbol(wrap)]

          rule wrap left a => wrap right b
        endmodule
    "#
);

injection_snapshot!(
    wraps_cell_sorts_with_set_elements,
    r#"
        module MAIN
          syntax Cell ::= "cell" [symbol(cell)]
          syntax Cells [hook(SET.Set)]
          syntax Cells ::= Cell
                         | "CellItem" "(" Cell ")" [symbol(CellItem), hook(SET.element)]
                         | Cells Cells [symbol(_Cells_), hook(SET.concat), comm, idem, element(CellItem), wrapElement(cell)]
          syntax Parent ::= "parent" Cells [symbol(parent)]

          rule parent cell => parent cell
        endmodule
    "#
);

injection_snapshot!(
    wraps_cell_sorts_with_map_keys_and_elements,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Entry ::= "entry" Int [symbol(entry)]
          syntax Entries [hook(MAP.Map)]
          syntax Entries ::= Entry
                           | "EntryItem" "(" Int "," Entry ")" [symbol(EntryItem), hook(MAP.element)]
                           | Entries Entries [symbol(_Entries_), hook(MAP.concat), comm, element(EntryItem), wrapElement(entry)]
          syntax Parent ::= "parent" Entries [symbol(parent)]

          rule parent entry 1 => parent entry 2
        endmodule
    "#
);

#[test]
fn lifts_nested_rewrites_before_adding_injections() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= "pair" "(" Exp "," Exp ")" [symbol(pair)]
        endmodule
    "#});
    let token = |value: &str| Term::Token {
        token: value.into(),
        sort: Sort::new("Int"),
    };
    let body = Term::apply(
        "pair",
        vec![
            Term::Rewrite {
                left: Box::new(token("1")),
                right: Box::new(token("2")),
            },
            token("3"),
        ],
    );
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let sentence = Sentence::Rule {
        body,
        requires: truth.clone(),
        ensures: truth,
        attributes: Attributes::default(),
    };
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injected = SortInjector::new(&resolved, "MAIN")
        .unwrap()
        .inject_sentence(&sentence)
        .unwrap();
    let Sentence::Rule { body, .. } = injected else {
        unreachable!()
    };
    assert_eq!(
        body.to_string(),
        "pair(inj{Int,Exp}(#token(\"1\",\"Int\")),inj{Int,Exp}(#token(\"3\",\"Int\")))=>pair(inj{Int,Exp}(#token(\"2\",\"Int\")),inj{Int,Exp}(#token(\"3\",\"Int\")))"
    );
}

#[test]
fn definition_sort_injections_carry_generation_receipts() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
                       | "pair" "(" Exp "," Exp ")" [symbol(pair)]
          rule pair(1, 3) => pair(2, 3) [label(injected)]
        endmodule
    "#});
    let injected = add_sort_injections_to_definition(&definition).unwrap();
    let receipt = injected
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| {
            (sentence.attributes().get_str("label") == Some("injected"))
                .then(|| sentence.attributes().get(ORIGIN_ATTRIBUTE))
                .flatten()
        })
        .expect("the injected rule should carry a receipt");

    assert_eq!(receipt["pass"], GeneratingPass::AddSortInjections.as_str());
}

#[test]
fn kitem_to_k_uses_a_sequence_without_an_injection() {
    let definition = lowered("module MAIN\nendmodule");
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let term = Term::InjectedLabel(Label::new("label"));
    let injected = SortInjector::new(&resolved, "MAIN")
        .unwrap()
        .inject(&term, &Sort::new("K"))
        .unwrap();

    assert!(matches!(
        injected,
        Term::Sequence(ref items)
            if matches!(items.as_slice(), [Term::InjectedLabel(label)] if label.name == "label")
    ));
}

#[test]
fn application_cast_context_does_not_replace_its_production_sort() {
    let definition = lowered(indoc! {r#"
        module MAIN
          syntax KItem ::= "project" [symbol(project)]
          syntax Cell ::= "cell" K [symbol(cell)]
        endmodule
    "#});
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let projected = Term::apply("project", vec![]).with_metadata(TermMetadata {
        sort: Some(Sort::new("K")),
        ..TermMetadata::default()
    });
    let term = Term::apply("cell", vec![projected]);
    let injected = SortInjector::new(&resolved, "MAIN")
        .unwrap()
        .inject_at_top(&term)
        .unwrap();

    let Term::Apply { arguments, .. } = injected.unannotated() else {
        panic!("expected cell application");
    };
    assert!(matches!(
        arguments.as_slice(),
        [Term::Sequence(items)]
            if matches!(items.as_slice(), [item]
                if matches!(item.unannotated(), Term::Apply { label, .. } if label.name == "project"))
    ));
}

#[test]
fn synthetic_unsorted_variables_use_expected_sort_then_k() {
    let definition = lowered("module MAIN\n  syntax Exp\nendmodule");
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let variable = Term::variable("X");

    assert_eq!(injector.term_sort(&variable, None).unwrap(), Sort::new("K"));
    assert_eq!(
        injector
            .term_sort(&variable, Some(&Sort::new("Exp")))
            .unwrap(),
        Sort::new("Exp")
    );
    assert!(matches!(
        injector.inject(&variable, &Sort::new("Exp")).unwrap(),
        Term::Variable { name, sort: Some(sort) } if name == "X" && sort == Sort::new("Exp")
    ));
    assert!(matches!(
        injector.inject_at_top(&variable).unwrap(),
        Term::Variable { name, sort: Some(sort) } if name == "X" && sort == Sort::new("K")
    ));
}

#[test]
fn synthetic_application_sort_metadata_projects_only_strict_subsorts() {
    let definition = generate_sort_projections(&lowered(indoc! {r#"
        module MAIN
          syntax Int ::= "int" [symbol(int)]
          syntax KItem ::= Int
                         | "item" [symbol(item)]
          syntax Other ::= "other" [symbol(other)]
        endmodule
    "#}))
    .unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let injector = SortInjector::new(&resolved, "MAIN").unwrap();
    let metadata = |sort| TermMetadata {
        sort: Some(Sort::new(sort)),
        ..TermMetadata::default()
    };

    let exact = Term::apply("item", vec![]).with_metadata(metadata("KItem"));
    let upcast = Term::apply("int", vec![]).with_metadata(metadata("KItem"));
    let downcast = Term::apply("item", vec![]).with_metadata(metadata("Int"));
    let unrelated = Term::apply("item", vec![]).with_metadata(metadata("Other"));

    let exact = injector.inject_at_top(&exact).unwrap().to_string();
    let upcast = injector
        .inject(&upcast, &Sort::new("KItem"))
        .unwrap()
        .to_string();
    let downcast = injector.inject_at_top(&downcast).unwrap().to_string();
    let unrelated = injector.inject_at_top(&unrelated).unwrap().to_string();

    assert_eq!(exact, "item(.KList)");
    assert_eq!(upcast, "inj{Int,KItem}(int(.KList))");
    // A downcast sorts as its target, so injecting it at its own sort adds no injection.
    assert_eq!(downcast, "`project:Int`(item(.KList))");
    assert_eq!(unrelated, "item(.KList)");
}

#[test]
fn flattens_nested_sequences_during_final_injection() {
    let definition = lowered("module MAIN\nendmodule");
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let term = Term::Sequence(vec![
        Term::Sequence(vec![Term::InjectedLabel(Label::new("first"))]),
        Term::Variable {
            name: "REST".into(),
            sort: Some(Sort::new("K")),
        },
    ]);
    let injected = SortInjector::new(&resolved, "MAIN")
        .unwrap()
        .inject(&term, &Sort::new("K"))
        .unwrap();

    assert!(matches!(
        injected,
        Term::Sequence(ref items) if items.len() == 2
    ));
}

#[test]
fn definition_injection_uses_the_selected_modules_visible_syntax() {
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            FlatModule {
                name: "BASE".into(),
                imports: vec![],
                local_sentences: vec![Arc::new(Sentence::Rule {
                    body: Term::Rewrite {
                        left: Box::new(Term::apply("consumerOnly", vec![])),
                        right: Box::new(Term::apply("consumerOnly", vec![])),
                    },
                    requires: truth.clone(),
                    ensures: truth,
                    attributes: Attributes::default(),
                })],
                attributes: Attributes::default(),
            },
            FlatModule {
                name: "MAIN".into(),
                imports: vec![FlatImport {
                    name: "BASE".into(),
                    public: true,
                }],
                local_sentences: vec![Arc::new(Sentence::Production {
                    label: Some(Label::new("consumerOnly")),
                    parameters: vec![],
                    sort: Sort::new("KItem"),
                    items: Vec::<ProductionItem>::new(),
                    attributes: Attributes::default(),
                })],
                attributes: Attributes::default(),
            },
        ],
        attributes: Attributes::default(),
    };

    let injected = add_sort_injections_to_definition(&definition).unwrap();
    let Sentence::Rule { body, .. } = &*injected.modules[0].local_sentences[0] else {
        panic!("expected imported rule");
    };
    assert_eq!(
        body.to_string(),
        "consumerOnly(.KList)=>consumerOnly(.KList)"
    );
}

#[test]
fn definition_injection_ignores_modules_outside_the_main_import_closure() {
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let unrelated_module = FlatModule {
        name: "UNRELATED".into(),
        imports: vec![],
        local_sentences: vec![Arc::new(Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply("unrelated", vec![])),
                right: Box::new(Term::apply("unrelated", vec![])),
            },
            requires: truth.clone(),
            ensures: truth,
            attributes: Attributes::default(),
        })],
        attributes: Attributes::default(),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            FlatModule {
                name: "MAIN".into(),
                imports: vec![],
                local_sentences: vec![],
                attributes: Attributes::default(),
            },
            unrelated_module.clone(),
        ],
        attributes: Attributes::default(),
    };

    let injected = add_sort_injections_to_definition(&definition).unwrap();

    assert_eq!(injected.modules[1], unrelated_module);
}

#[test]
fn definition_injection_errors_name_the_source_sentence() {
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let mut attributes = Attributes::default();
    attributes.insert(SOURCE_ATTRIBUTE, json!("fixture.k"));
    attributes.insert(LOCATION_ATTRIBUTE, json!([17, 3, 17, 18]));
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: vec![],
            local_sentences: vec![Arc::new(Sentence::Rule {
                body: Term::Rewrite {
                    left: Box::new(Term::apply("missing", vec![])),
                    right: Box::new(Term::apply("missing", vec![])),
                },
                requires: truth.clone(),
                ensures: truth,
                attributes,
            })],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    };

    let error = add_sort_injections_to_definition(&definition).unwrap_err();

    assert_eq!(
        error.to_string(),
        "fixture.k:17: cannot find a production for KLabel \"missing\""
    );
}

// A loaded rule edited in place and relinked, as an embedder that mutates `LoadedDefinition`
// does, and the same edited rule given to `load_structured` in place of its bubble: the compiler
// must reject every term whose sort does not fit its position, whatever path produced it.
mod edited_loaded_rules {
    use k_rust::builtin;
    use k_rust::definition::{AttributeKey, Definition, ResolvedDefinition, Sentence};
    use k_rust::kast::{Sort, Term};
    use k_rust::kompile::{
        CompilationBackend, CompileError, CompileOptions, compile_loaded_definition,
    };
    use k_rust::outer::{
        LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation, load_structured,
    };

    const COUNTER: &str = include_str!("fixtures/sort-check/counter.k");
    const PRELUDE: &str = include_str!("fixtures/sort-check/portable-prelude.k");
    const BACKENDS: [CompilationBackend; 2] = [CompilationBackend::Rust, CompilationBackend::Llvm];

    fn options(backend: CompilationBackend) -> LoadOptions {
        LoadOptions {
            implicit_sources: vec![
                builtin::embedded("kast.md").unwrap(),
                ResolvedSource::new("portable-prelude.k", PRELUDE.to_owned()),
            ],
            excluded_module_attributes: vec![backend.excluded_module_attribute().to_owned()],
            ..LoadOptions::default()
        }
    }

    fn load(backend: CompilationBackend) -> LoadedDefinition {
        let mut resolver = |_: &str, required: &str| {
            builtin::embedded(required).ok_or_else(|| required.to_owned())
        };
        load_for_compilation(
            ResolvedSource::new("counter.k", COUNTER.to_owned()),
            "COUNTER",
            None,
            &mut resolver,
            &options(backend),
        )
        .unwrap_or_else(|error| panic!("{error}"))
        .0
    }

    fn labelled<'a>(definition: &'a mut Definition, label: &str) -> &'a mut Sentence {
        let module = definition
            .modules
            .iter_mut()
            .find(|module| module.name == "COUNTER")
            .unwrap();
        let sentence = module
            .local_sentences
            .iter_mut()
            .find(|sentence| sentence.attributes().string(AttributeKey::Label) == Some(label))
            .unwrap();
        k_rust::definition::sentence_mut(sentence)
    }

    /// The subterm at `path`: 0 body, 1 requires; then rewrite sides and application arguments.
    fn at<'a>(sentence: &'a mut Sentence, path: &[usize]) -> &'a mut Term {
        let Sentence::Rule { body, requires, .. } = sentence else {
            panic!("expected a rule")
        };
        let mut term = if path[0] == 0 { body } else { requires };
        for step in &path[1..] {
            while let Term::Annotated { term: inner, .. } = term {
                term = inner;
            }
            term = match term {
                Term::Rewrite { left, right } => {
                    if *step == 0 {
                        left
                    } else {
                        right
                    }
                }
                Term::Apply { arguments, .. } => &mut arguments[*step],
                other => panic!("no child {step} in {other}"),
            };
        }
        term
    }

    fn token(value: &str, sort: &str) -> Term {
        Term::Token {
            token: value.into(),
            sort: Sort::new(sort),
        }
    }

    fn cast(sort: &str, term: Term) -> Term {
        Term::apply(format!("#SemanticCastTo{sort}"), vec![term])
    }

    fn compile(loaded: &LoadedDefinition, backend: CompilationBackend) -> Result<(), CompileError> {
        compile_loaded_definition(
            loaded,
            CompileOptions {
                backend,
                ..CompileOptions::default()
            },
        )
        .map(|_| ())
    }

    fn relinked(base: &LoadedDefinition, definition: Definition) -> LoadedDefinition {
        LoadedDefinition {
            files: base.files.clone(),
            source_table: base.source_table.clone(),
            resolved: ResolvedDefinition::resolve(&definition).expect("edited definition resolves"),
            definition,
            diagnostics: base.diagnostics.clone(),
        }
    }

    /// The edited `increment` rule spliced into the outer-lowered source in place of its bubble.
    fn structured(edited: Sentence, backend: CompilationBackend) -> LoadedDefinition {
        let parsed = k_rust::outer::parse("counter.k", COUNTER).unwrap();
        let mut definition = k_rust::outer::lower(&parsed, "COUNTER").unwrap();
        let module = definition
            .modules
            .iter_mut()
            .find(|module| module.name == "COUNTER")
            .unwrap();
        let bubble = module
            .local_sentences
            .iter_mut()
            .find(|sentence| {
                matches!(&***sentence, Sentence::Bubble { contents, .. }
                    if contents.contains("counter(N, s(L))"))
            })
            .expect("the increment bubble");
        *k_rust::definition::sentence_mut(bubble) = edited;
        load_structured(definition, &options(backend)).unwrap_or_else(|error| panic!("{error}"))
    }

    /// Compile `increment` with `replacement` at `path` through both entry paths and backends.
    fn outcomes(
        path: &[usize],
        replacement: &Term,
    ) -> Vec<(CompilationBackend, &'static str, Result<(), CompileError>)> {
        let mut outcomes = Vec::new();
        for backend in BACKENDS {
            let base = load(backend);
            let mut definition = base.definition.clone();
            let sentence = labelled(&mut definition, "COUNTER.increment");
            *at(sentence, path) = replacement.clone();
            let edited = sentence.clone();
            outcomes.push((
                backend,
                "relinked",
                compile(&relinked(&base, definition), backend),
            ));
            outcomes.push((
                backend,
                "load_structured",
                compile(&structured(edited, backend), backend),
            ));
        }
        outcomes
    }

    fn assert_rejected(path: &[usize], replacement: Term, reason: &str) {
        for (backend, entry, outcome) in outcomes(path, &replacement) {
            let error = outcome.expect_err(&format!(
                "{backend} {entry} compiled the ill-sorted {replacement}"
            ));
            assert_eq!(
                error.stage, "add sort injections",
                "{backend} {entry}: {error}"
            );
            assert!(
                error.message.contains("counter.k:16: ") && error.message.contains(reason),
                "{backend} {entry}: {error}"
            );
        }
    }

    fn assert_compiles(path: &[usize], replacement: Term) {
        for (backend, entry, outcome) in outcomes(path, &replacement) {
            outcome.unwrap_or_else(|error| {
                panic!("{backend} {entry} rejected {replacement}: {error}")
            });
        }
    }

    const NOT_A_SUBSORT: &str = "which is not a subsort of the sort";

    #[test]
    fn a_bool_token_at_a_nat_argument_is_rejected() {
        assert_rejected(
            &[0, 1, 0],
            token("true", "Bool"),
            &format!("has sort Bool, {NOT_A_SUBSORT} Nat"),
        );
    }

    #[test]
    fn a_requires_clause_of_a_user_sort_is_rejected() {
        assert_rejected(
            &[1],
            Term::apply("z", vec![]),
            &format!("has sort Nat, {NOT_A_SUBSORT} Bool"),
        );
    }

    #[test]
    fn an_int_requires_clause_is_rejected() {
        assert_rejected(
            &[1],
            token("1", "Int"),
            &format!("has sort Int, {NOT_A_SUBSORT} Bool"),
        );
    }

    #[test]
    fn an_application_requires_clause_of_another_sort_is_rejected() {
        let counter = Term::apply(
            "counter",
            vec![Term::apply("z", vec![]), Term::apply("z", vec![])],
        );
        assert_rejected(
            &[1],
            counter,
            &format!("has sort Counter, {NOT_A_SUBSORT} Bool"),
        );
    }

    #[test]
    fn a_counter_term_at_a_nat_argument_is_rejected() {
        let base = load(CompilationBackend::Rust);
        let mut definition = base.definition.clone();
        let left = at(labelled(&mut definition, "COUNTER.increment"), &[0, 0]).clone();
        assert_rejected(
            &[0, 1, 0],
            left,
            &format!("has sort Counter, {NOT_A_SUBSORT} Nat"),
        );
    }

    #[test]
    fn a_cast_to_a_sort_incomparable_with_its_operand_is_rejected() {
        assert_rejected(
            &[0, 1, 0],
            cast("Nat", token("true", "Bool")),
            "to sort Nat is not comparable with its sort Bool",
        );
    }

    // The cast alone makes the condition ill-sorted: `Nat` and `Bool` are incomparable, even though
    // the condition position accepts the operand's own sort.
    #[test]
    fn an_incomparable_cast_as_a_requires_clause_is_rejected() {
        assert_rejected(
            &[1],
            cast("Nat", token("true", "Bool")),
            "to sort Nat is not comparable with its sort Bool",
        );
    }

    #[test]
    fn the_unedited_definition_compiles() {
        for backend in BACKENDS {
            compile(&load(backend), backend).unwrap_or_else(|error| panic!("{backend}: {error}"));
        }
    }

    // `Counter` and `Bool` are both below `KItem`, their least upper bound, so the rewrite is well
    // sorted at `KItem`.
    #[test]
    fn a_rewrite_between_sibling_sorts_compiles_at_their_upper_bound() {
        assert_compiles(&[0, 1], token("true", "Bool"));
    }

    #[test]
    fn an_upcast_and_an_exact_cast_compile() {
        assert_compiles(&[0, 1, 0], cast("Nat", Term::apply("z", vec![])));
        assert_compiles(&[1], cast("KItem", token("true", "Bool")));
    }
}
