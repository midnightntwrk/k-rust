//! An equation is attempted only on a term its left-hand side's key does not refute
//! (`k_rust_backend::matching::LeftSideKey`), and a key refutes only a term the left-hand side
//! does not match.

use k_rust_backend::{
    definition::BackendDefinition,
    matching::{MatchMode, MatchResult, match_terms_in_definition},
    rule::RewriteRule,
    simplify::SimplificationOptions,
    term::Term,
};
use k_rust_kore::kore::parser::parse_definition;
use k_rust_kore::measure::{Counter, snapshot};

use crate::support::{internal_term, unstopped::simplify};

/// Sorts `A`, `B`, `C` and `Token` below `KItem`, with `C` below `A`; `Val` below `Exp`, with
/// the overloaded productions `app` (of `Exp`) and `appv` (of `Val`).
///
/// - `unwrap-A`: `kseq(inj{A, KItem}(projectA(I)), dotk()) = I`, a simplification, as a sort
///   projection's inverse is written;
/// - `unwrap-Exp`: the same for `Exp`;
/// - `pick-a1`, `pick-a2`: `pick(a1()) = b1()` and `pick(a2()) = b2()`, function equations with
///   a constructor argument;
/// - `plus-zero`: `plus(zero(), X) = X` on the commutative `plus`, whose arguments no key reads.
fn definition() -> BackendDefinition {
    let subsort = |sub: &str, sup: &str| {
        format!(
            r#"
            axiom{{R}} \exists{{R}}(Val:Sort{sup}{{}},
              \equals{{Sort{sup}{{}}, R}}(Val:Sort{sup}{{}},
                inj{{Sort{sub}{{}}, Sort{sup}{{}}}}(From:Sort{sub}{{}})))
              [subsort{{Sort{sub}{{}}, Sort{sup}{{}}}}()]"#
        )
    };
    let unwrap = |sort: &str| {
        format!(
            r#"
            axiom{{R}} \implies{{R}}(
              \top{{R}}(),
              \equals{{SortK{{}}, R}}(
                kseq{{}}(inj{{Sort{sort}{{}}, SortKItem{{}}}}(project{sort}{{}}(I:SortK{{}})), dotk{{}}()),
                \and{{SortK{{}}}}(I:SortK{{}}, \top{{SortK{{}}}}())
              )
            ) [label{{}}("unwrap-{sort}"), simplification{{}}()]"#
        )
    };
    let pick = |argument: &str, result: &str| {
        format!(
            r#"
            axiom{{R}} \implies{{R}}(
              \and{{R}}(
                \top{{R}}(),
                \and{{R}}(\in{{SortA{{}}, R}}(X0:SortA{{}}, {argument}{{}}()), \top{{R}}())
              ),
              \equals{{SortB{{}}, R}}(
                pick{{}}(X0:SortA{{}}),
                \and{{SortB{{}}}}({result}{{}}(), \top{{SortB{{}}}}())
              )
            ) [label{{}}("pick-{argument}")]"#
        )
    };
    let source = [
        r#"[]
        module MAIN
            sort SortK{} []
            sort SortKItem{} []
            sort SortA{} []
            sort SortB{} []
            sort SortC{} []
            sort SortExp{} []
            sort SortVal{} []
            sort SortToken{} [hasDomainValues{}()]
            symbol inj{From, To}(From) : To [sortInjection{}()]
            symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}(), total{}()]
            symbol dotk{}() : SortK{} [constructor{}(), total{}()]
            symbol a1{}() : SortA{} [constructor{}(), total{}()]
            symbol a2{}() : SortA{} [constructor{}(), total{}()]
            symbol b1{}() : SortB{} [constructor{}(), total{}()]
            symbol b2{}() : SortB{} [constructor{}(), total{}()]
            symbol c1{}() : SortC{} [constructor{}(), total{}()]
            symbol v{}() : SortVal{} [constructor{}(), total{}()]
            symbol appv{}(SortVal{}, SortVal{}) : SortVal{} [constructor{}(), total{}()]
            symbol app{}(SortExp{}, SortExp{}) : SortExp{}
                [anywhere{}(), functional{}(), injective{}(), no-evaluators{}()]
            symbol projectA{}(SortK{}) : SortA{} [function{}(), no-evaluators{}()]
            symbol projectExp{}(SortK{}) : SortExp{} [function{}(), no-evaluators{}()]
            symbol opaqueB{}(SortB{}) : SortB{} [function{}(), total{}(), no-evaluators{}()]
            symbol opaqueA{}(SortB{}) : SortA{} [function{}(), total{}(), no-evaluators{}()]
            symbol pick{}(SortA{}) : SortB{} [function{}()]
            symbol zero{}() : SortB{} [constructor{}(), total{}()]
            symbol plus{}(SortB{}, SortB{}) : SortB{} [function{}(), total{}(), comm{}()]
            axiom{R} \equals{SortB{}, R}(
                plus{}(X:SortB{}, Y:SortB{}), plus{}(Y:SortB{}, X:SortB{})) [comm{}()]
            axiom{} \equals{SortExp{}, SortExp{}}(
                app{}(inj{SortVal{}, SortExp{}}(V1:SortVal{}), inj{SortVal{}, SortExp{}}(V2:SortVal{})),
                inj{SortVal{}, SortExp{}}(appv{}(V1:SortVal{}, V2:SortVal{}))
            ) [symbol-overload{}(app{}(), appv{}())]
            axiom{R} \implies{R}(
              \top{R}(),
              \equals{SortB{}, R}(
                plus{}(zero{}(), X:SortB{}),
                \and{SortB{}}(X:SortB{}, \top{SortB{}}())
              )
            ) [label{}("plus-zero"), simplification{}()]"#
            .to_owned(),
        subsort("A", "KItem"),
        subsort("B", "KItem"),
        subsort("C", "KItem"),
        subsort("C", "A"),
        subsort("Token", "KItem"),
        subsort("Exp", "KItem"),
        subsort("Val", "KItem"),
        subsort("Val", "Exp"),
        unwrap("A"),
        unwrap("Exp"),
        pick("a1", "b1"),
        pick("a2", "b2"),
        "\nendmodule []".to_owned(),
    ]
    .concat();
    let syntax = parse_definition(&source).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

/// One item of sort `sort` on an empty rest.
fn item(sort: &str, operand: &str) -> String {
    format!("kseq{{}}(inj{{Sort{sort}{{}}, SortKItem{{}}}}({operand}), dotk{{}}())")
}

/// The subjects of the tests: every shape of argument a key reads or must not read.
fn subjects() -> Vec<String> {
    let app = "app{}(inj{SortVal{}, SortExp{}}(v{}()), inj{SortVal{}, SortExp{}}(v{}()))";
    vec![
        // A constructor of the left-hand side's sort, of an unrelated sort, of a subsort.
        item("A", "a1{}()"),
        item("B", "b1{}()"),
        item("C", "c1{}()"),
        // A domain value of an unrelated sort.
        item("Token", r#"\dv{SortToken{}}("5")"#),
        // The projection itself, a variable, and functions of the same and of another sort.
        item("A", "projectA{}(J:SortK{})"),
        item("A", "X:SortA{}"),
        item("B", "Y:SortB{}"),
        item("A", "opaqueA{}(b1{}())"),
        item("B", "opaqueB{}(b1{}())"),
        "kseq{}(Z:SortKItem{}, dotk{}())".to_owned(),
        // A rest that is not empty, and one that is a variable.
        "kseq{}(inj{SortA{}, SortKItem{}}(a1{}()), kseq{}(inj{SortB{}, SortKItem{}}(b1{}()), dotk{}()))"
            .to_owned(),
        "kseq{}(inj{SortB{}, SortKItem{}}(b1{}()), Rest:SortK{})".to_owned(),
        "kseq{}(inj{SortA{}, SortKItem{}}(projectA{}(J:SortK{})), Rest:SortK{})".to_owned(),
        // Overloaded productions: an overload equation may give them another root and sort.
        item("Val", "appv{}(v{}(), v{}())"),
        item("Val", "v{}()"),
        item("Exp", app),
        item("Exp", "projectExp{}(J:SortK{})"),
        // Function applications.
        "pick{}(a1{}())".to_owned(),
        "pick{}(a2{}())".to_owned(),
        "pick{}(X:SortA{})".to_owned(),
        "pick{}(opaqueA{}(b1{}()))".to_owned(),
        "pick{}(inj{SortC{}, SortA{}}(c1{}()))".to_owned(),
        "plus{}(b1{}(), zero{}())".to_owned(),
        "plus{}(zero{}(), b1{}())".to_owned(),
    ]
}

fn equations(definition: &BackendDefinition) -> Vec<&RewriteRule> {
    definition
        .function_theory()
        .values()
        .chain(definition.simplification_theory().values())
        .flat_map(|groups| groups.values().flatten())
        .map(|rule| &**rule)
        .collect()
}

fn equation<'d>(definition: &'d BackendDefinition, label: &str) -> &'d RewriteRule {
    equations(definition)
        .into_iter()
        .find(|rule| rule.attributes.label.as_deref() == Some(label))
        .unwrap_or_else(|| panic!("the definition has the equation {label}"))
}

fn refuted(definition: &BackendDefinition, label: &str, subject: &Term) -> bool {
    equation(definition, label)
        .computed_attributes
        .left_side_key
        .refutes(definition, subject)
        .is_some()
}

/// The equation attempts of simplifying `subject`, and the result.
fn attempts(definition: &BackendDefinition, subject: &Term) -> (u64, Term) {
    let before = snapshot();
    let result = simplify(definition, subject, SimplificationOptions::default())
        .expect("the simplification gives a term");
    let attempts = snapshot()
        .delta(&before)
        .get(Counter::SimplifyEquationAttempts);
    (attempts, result.term)
}

/// Every pair of an equation and a subject the key refutes is one the matcher fails: the scan
/// reads the key as the failed match of the left-hand side, so it may hold of no other pair.
#[test]
fn a_key_refutes_only_a_subject_the_left_hand_side_fails_to_match() {
    let definition = definition();
    let mut refutations = 0;
    for source in subjects() {
        let subject = internal_term(&definition, &source);
        for rule in equations(&definition) {
            if rule
                .computed_attributes
                .left_side_key
                .refutes(&definition, &subject)
                .is_none()
            {
                continue;
            }
            refutations += 1;
            let matched =
                match_terms_in_definition(MatchMode::Evaluate, &definition, &rule.lhs, &subject);
            assert!(
                matches!(matched, MatchResult::Failed(_)),
                "the key of {:?} refutes {source}, which the matcher gives {matched:?}",
                rule.attributes.label
            );
        }
    }
    assert!(refutations >= 10, "the subjects exercise the keys");
}

/// The key of `kseq(inj{A, KItem}(projectA(I)), dotk())` refutes an item whose root fixes a
/// sort that is not `A` or below it, and a rest whose root is not `dotk`; it refutes nothing
/// whose value the root leaves open.
#[test]
fn an_item_key_reads_the_sort_of_a_rigid_operand_and_the_root_of_the_rest() {
    let definition = definition();
    let refuted =
        |source: &str| refuted(&definition, "unwrap-A", &internal_term(&definition, source));
    // A constructor or a domain value of a sort that is not below `A`.
    assert!(refuted(&item("B", "b1{}()")));
    assert!(refuted(&item("Token", r#"\dv{SortToken{}}("5")"#)));
    // A rest that is another item.
    assert!(refuted(
        "kseq{}(inj{SortA{}, SortKItem{}}(projectA{}(J:SortK{})), kseq{}(inj{SortB{}, SortKItem{}}(b1{}()), dotk{}()))"
    ));
    // The sort itself and a subsort: `projectA(I)` may be that value.
    assert!(!refuted(&item("A", "a1{}()")));
    assert!(!refuted(&item("C", "c1{}()")));
    // A variable and a function application denote values of sorts their roots do not fix.
    assert!(!refuted(&item("B", "Y:SortB{}")));
    assert!(!refuted(&item("B", "opaqueB{}(b1{}())")));
    assert!(!refuted("kseq{}(Z:SortKItem{}, dotk{}())"));
    assert!(!refuted(
        "kseq{}(inj{SortA{}, SortKItem{}}(projectA{}(J:SortK{})), Rest:SortK{})"
    ));
    // An overloaded production may equal an application of another production.
    assert!(!refuted(&item("Val", "appv{}(v{}(), v{}())")));
}

/// A function equation with a constructor argument is keyed by it; an equation of a function
/// with algebraic axioms has no key, since its arguments do not individuate its applications.
#[test]
fn a_function_key_reads_constructor_arguments_unless_the_function_is_algebraic() {
    let definition = definition();
    let term = |source: &str| internal_term(&definition, source);
    assert!(refuted(&definition, "pick-a1", &term("pick{}(a2{}())")));
    assert!(!refuted(&definition, "pick-a1", &term("pick{}(a1{}())")));
    assert!(!refuted(&definition, "pick-a1", &term("pick{}(X:SortA{})")));
    assert!(!refuted(
        &definition,
        "pick-a1",
        &term("pick{}(opaqueA{}(b1{}()))")
    ));
    assert!(!refuted(
        &definition,
        "plus-zero",
        &term("plus{}(b1{}(), zero{}())")
    ));
}

/// A refuted equation is not attempted, and the term is what an attempt would have left: one
/// item of an unrelated sort is tried against neither projection's inverse, and `pick(a2())`
/// is evaluated by one attempt.
#[test]
fn a_refuted_equation_is_not_attempted() {
    let definition = definition();
    let unrelated = internal_term(&definition, &item("B", "b1{}()"));
    assert_eq!(attempts(&definition, &unrelated), (0, unrelated.clone()));

    let stuck = internal_term(&definition, &item("A", "projectA{}(J:SortK{})"));
    let (stuck_attempts, unwrapped) = attempts(&definition, &stuck);
    assert_eq!(unwrapped, internal_term(&definition, "J:SortK{}"));
    assert!(stuck_attempts >= 1);

    let picked = internal_term(&definition, "pick{}(a2{}())");
    assert_eq!(
        attempts(&definition, &picked),
        (1, internal_term(&definition, "b2{}()"))
    );
}
