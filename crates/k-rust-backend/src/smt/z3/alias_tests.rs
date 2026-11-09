use super::*;
use crate::{
    definition::BackendDefinition,
    smt::aliases,
    stop::{CancellationToken, StopCause},
    term::Variable,
};
use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

const SOURCE: &str = r#"[] module MAIN
  hooked-sort SortInt{} [hook{}("INT.Int"),hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"),hasDomainValues{}()]
  hooked-sort SortMap{} [hook{}("MAP.Map"),unit{}(unit{}()),element{}(item{}()),concat{}(concat{}())]
  hooked-symbol unit{}() : SortMap{} [function{}(),total{}(),hook{}("MAP.unit")]
  hooked-symbol item{}(SortInt{},SortInt{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.element")]
  hooked-symbol concat{}(SortMap{},SortMap{}) : SortMap{} [function{}(),hook{}("MAP.concat"),assoc{}(),comm{}()]
  hooked-symbol put{}(SortMap{},SortInt{},SortInt{}) : SortMap{} [function{}(),total{}(),hook{}("MAP.update")]
  hooked-symbol get{}(SortMap{},SortInt{}) : SortInt{} [function{}(),hook{}("MAP.lookup")]
  hooked-symbol member{}(SortInt{},SortMap{}) : SortBool{} [function{}(),total{}(),hook{}("MAP.in_keys")]
  symbol outer{}(SortInt{}) : SortInt{} [function{}(),total{}()]
  symbol pair{}(SortInt{},SortInt{}) : SortInt{} [function{}(),total{}()]
  symbol effect{}() : SortInt{} [function{}(),total{}(),impure{}()]
endmodule []"#;

fn definition(text: &str) -> BackendDefinition {
    BackendDefinition::internalize(&parse_definition(text).unwrap(), "MAIN").unwrap()
}
fn term(d: &BackendDefinition, text: &str) -> Term {
    d.internalize_term(&parse_pattern(text).unwrap(), &[])
        .unwrap()
}
fn equality(d: &BackendDefinition, a: &str, b: &str) -> Predicate {
    Predicate::Equals(term(d, a), term(d, b))
}
const BASE: &str = "get{}(M:SortMap{},J:SortInt{})";
const UPDATED: &str = "get{}(put{}(M:SortMap{},K:SortInt{},V:SortInt{}),J:SortInt{})";
fn framed(d: &BackendDefinition) -> Vec<Predicate> {
    vec![
        Predicate::Ceil(term(d, BASE)),
        Predicate::Not(Arc::new(equality(d, "K:SortInt{}", "J:SortInt{}"))),
    ]
}

#[test]
fn proved_map_observation_aliases_compose_under_an_opaque_scalar_function() {
    let d = definition(SOURCE);
    let solver = Z3Solver::new(&d).unwrap();
    let checked = [equality(
        &d,
        &format!("outer{{}}({UPDATED})"),
        &format!("outer{{}}({BASE})"),
    )];
    assert_eq!(
        solver.prove_with_observation_aliases(&framed(&d), &Substitution::new(), &checked),
        Ok(true)
    );
    assert_eq!(
        solver.check_predicates(&framed(&d), &Substitution::new(), &checked),
        Ok(Ok(Validity::Valid))
    );
}

#[test]
fn true_or_unknown_key_aliases_cannot_assume_the_preserved_base_read() {
    let d = definition(SOURCE);
    for alias in [true, false] {
        let mut known = vec![
            Predicate::Ceil(term(&d, BASE)),
            equality(&d, BASE, r#"\dv{SortInt{}}("0")"#),
            equality(&d, "V:SortInt{}", r#"\dv{SortInt{}}("1")"#),
        ];
        if alias {
            known.push(equality(&d, "K:SortInt{}", "J:SortInt{}"));
        }
        let solver = Z3Solver::new(&d).unwrap();
        assert_eq!(
            solver.prove_with_observation_aliases(
                &known,
                &Substitution::new(),
                &[equality(&d, UPDATED, BASE)]
            ),
            Ok(false)
        );
    }
}

#[test]
fn missing_reads_and_strict_undefined_writes_do_not_become_defined_aliases() {
    let d = definition(SOURCE);
    let missing = Predicate::Not(Arc::new(Predicate::Ceil(term(&d, BASE))));
    let mut known = framed(&d);
    known[0] = missing;
    let solver = Z3Solver::new(&d).unwrap();
    assert_eq!(
        solver.prove_with_observation_aliases(
            &known,
            &Substitution::new(),
            &[Predicate::Not(Arc::new(Predicate::Ceil(term(&d, UPDATED))))]
        ),
        Ok(false)
    );
    let value = term(&d, "get{}(N:SortMap{},P:SortInt{})");
    let mut known = framed(&d);
    known.push(Predicate::Not(Arc::new(Predicate::Ceil(value))));
    let strict = "get{}(put{}(M:SortMap{},K:SortInt{},get{}(N:SortMap{},P:SortInt{})),J:SortInt{})";
    assert_eq!(
        solver.prove_with_observation_aliases(
            &known,
            &Substitution::new(),
            &[equality(&d, strict, BASE)]
        ),
        Ok(false)
    );
}

#[test]
fn source_ownership_effects_binders_and_large_shared_graphs_decline_discovery() {
    let d = definition(SOURCE);
    let prelude = SmtPrelude::from_definition(&d).unwrap();
    let other = definition(SOURCE);
    let foreign = Predicate::Equals(term(&other, UPDATED), term(&d, BASE));
    assert!(aliases::discover(&prelude, &[foreign]).unwrap().is_none());
    let effect = "get{}(put{}(M:SortMap{},K:SortInt{},effect{}()),J:SortInt{})";
    assert!(
        aliases::discover(&prelude, &[equality(&d, effect, BASE)])
            .unwrap()
            .is_none()
    );
    let bound = Predicate::Exists(
        Variable::new("K", term(&d, "K:SortInt{}").sort()),
        Arc::new(equality(&d, UPDATED, BASE)),
    );
    assert!(aliases::discover(&prelude, &[bound]).unwrap().is_none());
    let changed = definition(&SOURCE.replace(
        "hook{}(\"MAP.lookup\")",
        "hook{}(\"MAP.lookup\"),impure{}()",
    ));
    assert!(
        aliases::discover(
            &SmtPrelude::from_definition(&changed).unwrap(),
            &[equality(&changed, UPDATED, BASE)]
        )
        .unwrap()
        .is_none()
    );
    let mut large = term(&d, UPDATED);
    for _ in 0..30 {
        large = Term::application(
            d.symbols()["pair"].clone(),
            vec![],
            vec![large.clone(), large],
        );
    }
    assert!(
        aliases::discover(&prelude, &[Predicate::Equals(large.clone(), large)])
            .unwrap()
            .is_none()
    );
    let token = CancellationToken::new();
    token.cancel();
    assert_eq!(
        token
            .scope(|| aliases::discover(&prelude, &[]))
            .map_err(Stop::into_cause)
            .map(|_| ())
            .unwrap_err(),
        StopCause::Cancelled
    );
}
