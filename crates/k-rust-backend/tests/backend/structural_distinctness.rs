//! Structural distinctness of ground terms (`Term::structurally_distinct_after_normalization`)
//! and the callers that refute through it: predicate simplification of `\equals` and the pairwise
//! disequalities `ceil_term` emits for set elements.
//!
//! A ground term whose heads are constructors or `anywhere` productions is not thereby a normal
//! form: with the anywhere equation `wrap(s(X)) = wrap(X)`, the ground `wrap(s(z))` equals
//! `wrap(z)`. Only an `anywhere` application the simplifier certified as a fixed point (its
//! `evaluated` bit) may decide an equality; constructor-only terms decide it as before.

use k_rust_backend::{
    definedness::ceil_term,
    definition::BackendDefinition,
    rule::Predicate,
    simplify::{SimplificationOptions, simplify, simplify_predicate_with_solver},
    smt::{NoSolver, SmtError, SmtSolver, Validity},
    substitution::Substitution,
    term::Term,
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::internal_term;

/// `z`, `s`, `addr`, `sub`, `cell`, `spare` and `item` are constructors; `wrap` and `tag` are
/// `anywhere` productions (`wrap` with the `injective` attribute kompile emits, `tag` without
/// it); `wrap` carries the anywhere equation `wrap(s(X)) = wrap(X)`, with the requires clause
/// `condition() = true` when `guarded`; `tag` has no equation. `SortSub` is a subsort of
/// `SortAddress`; `SortNat` and `SortAddress` share no subsort.
fn definition(guarded: bool) -> BackendDefinition {
    definition_with(guarded, "")
}

/// [`definition`] with `attribute` (a KORE attribute such as `concrete{}()`, or empty) added to
/// the `unwrap` equation, and an anywhere production `pick` of sort `SortNat` without equations.
fn definition_with(guarded: bool, attribute: &str) -> BackendDefinition {
    internalized(&definition_source(guarded, attribute))
}

fn internalized(source: &str) -> BackendDefinition {
    let syntax = parse_definition(source).expect("definition should parse");
    BackendDefinition::internalize(&syntax, "MAIN").expect("definition should internalize")
}

/// The source of [`definition_with`].
fn definition_source(guarded: bool, attribute: &str) -> String {
    let attribute = if attribute.is_empty() {
        String::new()
    } else {
        format!(", {attribute}")
    };
    let requires = if guarded {
        r#"\equals{SortBool{}, R}(condition{}(), \dv{SortBool{}}("true"))"#
    } else {
        r#"\top{R}()"#
    };
    format!(
        r#"[]
            module MAIN
                sort SortNat{{}} []
                sort SortAddress{{}} []
                sort SortCell{{}} []
                sort SortSub{{}} []
                sort SortKItem{{}} []
                symbol inj{{From, To}}(From) : To [sortInjection{{}}()]
                axiom{{R}} \exists{{R}}(
                    Value:SortAddress{{}},
                    \equals{{SortAddress{{}}, R}}(
                        Value:SortAddress{{}},
                        inj{{SortSub{{}}, SortAddress{{}}}}(From:SortSub{{}})
                    )
                ) [subsort{{SortSub{{}}, SortAddress{{}}}}()]
                axiom{{R}} \exists{{R}}(
                    Value:SortKItem{{}},
                    \equals{{SortKItem{{}}, R}}(Value:SortKItem{{}}, inj{{SortSub{{}}, SortKItem{{}}}}(From:SortSub{{}}))
                ) [subsort{{SortSub{{}}, SortKItem{{}}}}()]
                axiom{{R}} \exists{{R}}(
                    Value:SortKItem{{}},
                    \equals{{SortKItem{{}}, R}}(Value:SortKItem{{}}, inj{{SortNat{{}}, SortKItem{{}}}}(From:SortNat{{}}))
                ) [subsort{{SortNat{{}}, SortKItem{{}}}}()]
                axiom{{R}} \exists{{R}}(
                    Value:SortKItem{{}},
                    \equals{{SortKItem{{}}, R}}(Value:SortKItem{{}}, inj{{SortAddress{{}}, SortKItem{{}}}}(From:SortAddress{{}}))
                ) [subsort{{SortAddress{{}}, SortKItem{{}}}}()]
                symbol sub{{}}() : SortSub{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol item{{}}(SortKItem{{}}) : SortCell{{}}
                    [constructor{{}}(), functional{{}}(), injective{{}}()]
                hooked-sort SortBool{{}} [hook{{}}("BOOL.Bool"), hasDomainValues{{}}()]
                hooked-sort SortCellSet{{}}
                    [hook{{}}("SET.Set"), unit{{}}(setUnit{{}}()), element{{}}(setItem{{}}()),
                     concat{{}}(setConcat{{}}())]
                symbol z{{}}() : SortNat{{}} [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol s{{}}(SortNat{{}}) : SortNat{{}}
                    [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol wrap{{}}(SortNat{{}}) : SortAddress{{}}
                    [anywhere{{}}(), functional{{}}(), injective{{}}()]
                symbol tag{{}}(SortNat{{}}) : SortAddress{{}} [anywhere{{}}(), functional{{}}()]
                symbol pick{{}}(SortNat{{}}) : SortNat{{}} [anywhere{{}}(), functional{{}}()]
                symbol addr{{}}(SortNat{{}}) : SortAddress{{}}
                    [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol cell{{}}(SortAddress{{}}) : SortCell{{}}
                    [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol spare{{}}(SortAddress{{}}) : SortCell{{}}
                    [constructor{{}}(), functional{{}}(), injective{{}}()]
                symbol condition{{}}() : SortBool{{}} [function{{}}(), total{{}}(), no-evaluators{{}}()]
                hooked-symbol setUnit{{}}() : SortCellSet{{}}
                    [function{{}}(), total{{}}(), hook{{}}("SET.unit")]
                hooked-symbol setItem{{}}(SortCell{{}}) : SortCellSet{{}}
                    [function{{}}(), total{{}}(), hook{{}}("SET.element")]
                hooked-symbol setConcat{{}}(SortCellSet{{}}, SortCellSet{{}}) : SortCellSet{{}}
                    [function{{}}(), hook{{}}("SET.concat"), assoc{{}}(), comm{{}}(), idem{{}}()]
                axiom{{R}} \implies{{R}}(
                    \and{{R}}(
                        {requires},
                        \and{{R}}(\in{{SortNat{{}}, R}}(X0:SortNat{{}}, s{{}}(X:SortNat{{}})), \top{{R}}())
                    ),
                    \equals{{SortAddress{{}}, R}}(
                        wrap{{}}(X0:SortNat{{}}),
                        \and{{SortAddress{{}}}}(wrap{{}}(X:SortNat{{}}), \top{{SortAddress{{}}}}())
                    )
                ) [label{{}}("unwrap"), anywhere{{}}(){attribute}]
            endmodule []"#
    )
}

/// A solver that answers every validity query with the same verdict.
struct FixedValiditySolver(Validity);

impl SmtSolver for FixedValiditySolver {
    fn is_sat(
        &self,
        _predicates: &[Predicate],
        _substitution: &Substitution,
    ) -> Result<k_rust_backend::smt::Satisfiability, SmtError> {
        unreachable!()
    }

    fn check_predicates(
        &self,
        _known: &[Predicate],
        _substitution: &Substitution,
        _checked: &[Predicate],
    ) -> Result<Validity, SmtError> {
        Ok(self.0.clone())
    }
}

fn simplified(definition: &BackendDefinition, source: &str) -> Term {
    simplify(
        definition,
        &internal_term(definition, source),
        SimplificationOptions::default(),
    )
    .expect("the term should simplify")
    .term
}

fn simplify_equality(
    definition: &BackendDefinition,
    left: &str,
    right: &str,
    solver: &dyn SmtSolver,
) -> Predicate {
    simplify_predicate_with_solver(
        definition,
        &Predicate::Equals(
            internal_term(definition, left),
            internal_term(definition, right),
        ),
        &[],
        SimplificationOptions::default(),
        solver,
    )
    .expect("the equality should simplify")
}

fn set_of_cells(definition: &BackendDefinition, left: &str, right: &str) -> Term {
    internal_term(
        definition,
        &format!("setConcat{{}}(setItem{{}}(cell{{}}({left})), setItem{{}}(cell{{}}({right})))"),
    )
}

fn has_disequality(predicates: &[Predicate]) -> bool {
    predicates
        .iter()
        .any(|predicate| matches!(predicate, Predicate::Not(inner) if matches!(**inner, Predicate::Equals(..))))
}

const REDEX: &str = "wrap{}(s{}(z{}()))";
const NORMAL: &str = "wrap{}(z{}())";

#[test]
fn an_unnormalized_ground_anywhere_redex_is_not_structurally_distinct() {
    let definition = definition(false);
    let redex = internal_term(&definition, REDEX);
    let normal = internal_term(&definition, NORMAL);
    assert!(redex.concrete_after_normalization());

    assert!(!redex.structurally_distinct_after_normalization(&normal));
    assert!(
        !internal_term(&definition, &format!("cell{{}}({REDEX})"))
            .structurally_distinct_after_normalization(&internal_term(
                &definition,
                &format!("cell{{}}({NORMAL})")
            ))
    );
}

#[test]
fn constructor_terms_and_certified_anywhere_normal_forms_stay_structurally_distinct() {
    let definition = definition(false);
    let distinct =
        |left: &Term, right: &Term| left.structurally_distinct_after_normalization(right);
    let term = |source: &str| internal_term(&definition, source);

    assert!(distinct(&term("s{}(z{}())"), &term("z{}()")));
    assert!(distinct(
        &term("addr{}(s{}(z{}()))"),
        &term("addr{}(z{}())")
    ));
    // Distinct constructor heads decide whatever lies below them.
    assert!(distinct(
        &term(&format!("cell{{}}({REDEX})")),
        &term(&format!("spare{{}}({REDEX})"))
    ));
    // An uncertified anywhere application may normalize to any head of its sort.
    assert!(!distinct(&term(REDEX), &term("addr{}(z{}())")));
    // `tag` has no equation, so the simplifier certifies its applications as normal forms, and
    // two normal forms with different arguments are different values without `injective`.
    let tag_one = simplified(&definition, "tag{}(s{}(z{}()))");
    let tag_zero = simplified(&definition, "tag{}(z{}())");
    assert!(tag_one.attributes().evaluated);
    assert!(distinct(&tag_one, &tag_zero));
    assert!(!distinct(&term("tag{}(s{}(z{}()))"), &term("tag{}(z{}())")));
    let wrapped = simplified(&definition, NORMAL);
    assert!(wrapped.attributes().evaluated);
    assert!(distinct(&wrapped, &tag_zero));
}

#[test]
fn predicate_simplification_does_not_refute_an_anywhere_redex_equality() {
    // The equation normalizes both sides to `wrap(z)`.
    assert_eq!(
        simplify_equality(&definition(false), REDEX, NORMAL, &NoSolver),
        Predicate::True
    );

    // With an undecided requires clause the simplifier leaves `wrap(s(z))` as it is, a fixed
    // point that is not a normal form: `wrap(s(z)) = wrap(z)` holds when `condition()` does.
    let guarded = definition(true);
    let result = simplify_equality(
        &guarded,
        REDEX,
        NORMAL,
        &FixedValiditySolver(Validity::Indeterminate),
    );
    assert_ne!(result, Predicate::False);
    assert!(!matches!(result, Predicate::True));
}

#[test]
fn predicate_simplification_still_refutes_constructor_and_normal_form_equalities() {
    let definition = definition(true);
    let solver = FixedValiditySolver(Validity::Indeterminate);
    assert_eq!(
        simplify_equality(&definition, "s{}(z{}())", "z{}()", &solver),
        Predicate::False
    );
    assert_eq!(
        simplify_equality(&definition, "tag{}(s{}(z{}()))", "tag{}(z{}())", &solver),
        Predicate::False
    );
    assert_eq!(
        simplify_equality(
            &definition,
            "cell{}(tag{}(z{}()))",
            "cell{}(wrap{}(z{}()))",
            &solver
        ),
        Predicate::False
    );
}

#[test]
fn set_definedness_keeps_the_disequality_of_an_anywhere_redex_and_its_normal_form() {
    let definition = definition(false);
    let set = set_of_cells(&definition, REDEX, NORMAL);

    assert!(has_disequality(&ceil_term(&definition, &set)));

    // The same elements after normalization: `wrap(s(z))` becomes `wrap(z)` and the set
    // collapses to one element, which is defined.
    let simplified = simplify_predicate_with_solver(
        &definition,
        &Predicate::Ceil(set),
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("the set definedness predicate should simplify");
    assert_eq!(simplified, Predicate::True);
}

#[test]
fn set_definedness_still_separates_constructor_and_certified_elements() {
    let definition = definition(false);
    let constructors = set_of_cells(&definition, "addr{}(s{}(z{}()))", "addr{}(z{}())");
    assert!(!has_disequality(&ceil_term(&definition, &constructors)));

    // Before simplification the `tag` applications carry no normal-form certificate; after it,
    // they and `wrap(z)` are certified normal forms, separated without a residual disequality.
    let fresh = set_of_cells(&definition, "tag{}(s{}(z{}()))", "tag{}(z{}())");
    assert!(has_disequality(&ceil_term(&definition, &fresh)));
    for (left, right) in [
        ("tag{}(s{}(z{}()))", "tag{}(z{}())"),
        (NORMAL, "tag{}(z{}())"),
    ] {
        let set = simplify(
            &definition,
            &set_of_cells(&definition, left, right),
            SimplificationOptions::default(),
        )
        .expect("the set should simplify")
        .term;
        assert!(
            !has_disequality(&ceil_term(&definition, &set)),
            "{left}, {right}"
        );
    }
}

/// An injection pair with different sources is decided through the sort graph where that needs
/// no normal form, and otherwise only through certified normal forms.
#[test]
fn injections_are_separated_by_sorts_and_certified_normal_forms_only() {
    let solver = FixedValiditySolver(Validity::Indeterminate);
    let guarded = definition(true);
    // `SortNat` and `SortAddress` share no subsort: no value of one is a value of the other,
    // whatever `wrap(s(z))` normalizes to.
    assert_eq!(
        simplify_equality(
            &guarded,
            "item{}(inj{SortNat{}, SortKItem{}}(z{}()))",
            &format!("item{{}}(inj{{SortAddress{{}}, SortKItem{{}}}}({REDEX}))"),
            &solver,
        ),
        Predicate::False
    );
    // `SortSub` is a subsort of `SortAddress`: the pair is `inj{SortSub, SortAddress}(sub())`
    // against `wrap(s(z))`, which an anywhere equation may rewrite to that injection.
    let sub = "item{}(inj{SortSub{}, SortKItem{}}(sub{}()))";
    let wrapped = format!("item{{}}(inj{{SortAddress{{}}, SortKItem{{}}}}({REDEX}))");
    let undecided = simplify_equality(&guarded, sub, &wrapped, &solver);
    assert_ne!(undecided, Predicate::False);
    assert!(has_disequality(&ceil_term(
        &guarded,
        &internal_term(
            &guarded,
            &format!("setConcat{{}}(setItem{{}}({sub}), setItem{{}}({wrapped}))"),
        ),
    )));
    // Once `wrap(s(z))` is normalized to the certified `wrap(z)`, a normal form headed by an
    // anywhere production is not the value of an injection.
    assert_eq!(
        simplify_equality(&definition(false), sub, &wrapped, &NoSolver),
        Predicate::False
    );
}

#[test]
fn a_constructor_application_is_not_an_injection_but_an_uncertified_anywhere_one_may_be() {
    let definition = definition(false);
    let injected = internal_term(&definition, "inj{SortSub{}, SortAddress{}}(sub{}())");
    assert!(
        internal_term(&definition, "addr{}(z{}())")
            .structurally_distinct_after_normalization(&injected)
    );
    assert!(
        !internal_term(&definition, NORMAL).structurally_distinct_after_normalization(&injected)
    );
    assert!(simplified(&definition, NORMAL).structurally_distinct_after_normalization(&injected));
}

/// `concrete` and `symbolic` choose when the evaluator uses an equation; the equation still
/// holds. Under `wrap(s(X)) = wrap(X) [symbolic]` the ground `wrap(s(z))` equals `wrap(z)` although
/// the evaluator does not rewrite it, and under `[concrete]` (which the evaluator reads as
/// "bound to a constructor-like term") `wrap(s(pick(z)))` equals `wrap(pick(z))`. Neither
/// subject may be certified as a normal form, so neither equality is refuted.
#[test]
fn an_equation_set_aside_by_concrete_or_symbolic_withholds_the_normal_form_certificate() {
    for (attribute, subject, equal) in [
        ("symbolic{}()", REDEX, NORMAL),
        (
            "concrete{}()",
            "wrap{}(s{}(pick{}(z{}())))",
            "wrap{}(pick{}(z{}()))",
        ),
    ] {
        let definition = definition_with(false, attribute);
        let left = simplified(&definition, subject);
        let right = simplified(&definition, equal);
        assert!(
            !left.attributes().evaluated,
            "{attribute}: {subject} must not be certified"
        );
        assert!(
            !left.structurally_distinct_after_normalization(&right),
            "{attribute}: {subject} and {equal} are equal under the equation"
        );
        let equality = simplify_equality(&definition, subject, equal, &NoSolver);
        assert_ne!(
            equality,
            Predicate::False,
            "{attribute}: {subject} = {equal} holds under the equation"
        );
    }
}

/// Without the attribute the evaluator applies the equation, and the normal forms it reaches
/// are certified as before.
#[test]
fn the_same_equation_without_the_attribute_is_applied_and_certifies_its_result() {
    let definition = definition_with(false, "");
    let left = simplified(&definition, "wrap{}(s{}(pick{}(z{}())))");
    let right = simplified(&definition, "wrap{}(pick{}(z{}()))");
    assert_eq!(left, right);
    assert!(left.attributes().evaluated);
    assert_eq!(
        simplify_equality(
            &definition,
            "wrap{}(s{}(pick{}(z{}())))",
            "wrap{}(pick{}(z{}()))",
            &NoSolver
        ),
        Predicate::True
    );
}

/// A simplification whose left-hand side is a conjunction of term patterns is filed in the
/// predicate theory, so the term simplifier never tries it on an application, although it states
/// an equation between terms. Here the simplification `\and(tag(s(X)), tag(s(X))) = tag(X)` (hand-written
/// KORE; kompile never emits this shape) makes `tag(s(z))` equal to `tag(z)`. `tag` has no other
/// equation, so every offered scan fails. A definition holding such an equation certifies no
/// application, so `tag(s(z)) = tag(z)` is not refuted.
#[test]
fn a_conjunctive_left_hand_side_the_index_files_apart_withholds_every_certificate() {
    let lemma = r#"
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortAddress{}, R}(
                        \and{SortAddress{}}(tag{}(s{}(X:SortNat{})), tag{}(s{}(X:SortNat{}))),
                        \and{SortAddress{}}(tag{}(X:SortNat{}), \top{SortAddress{}}())
                    )
                ) [simplification{}()]
            endmodule []"#;
    let source = definition_source(false, "").replace("\n            endmodule []", lemma);
    assert!(source.contains("simplification{}()"));
    let definition = internalized(&source);
    for subject in ["tag{}(s{}(z{}()))", "tag{}(z{}())", REDEX] {
        assert!(
            !simplified(&definition, subject).attributes().evaluated,
            "{subject} must not be certified"
        );
    }
    assert_ne!(
        simplify_equality(&definition, "tag{}(s{}(z{}()))", "tag{}(z{}())", &NoSolver),
        Predicate::False
    );
    // Without the lemma the same applications are certified and the equality is refuted.
    let plain = definition_with(false, "");
    assert!(
        simplified(&plain, "tag{}(s{}(z{}()))")
            .attributes()
            .evaluated
    );
    assert_eq!(
        simplify_equality(&plain, "tag{}(s{}(z{}()))", "tag{}(z{}())", &NoSolver),
        Predicate::False
    );
}
