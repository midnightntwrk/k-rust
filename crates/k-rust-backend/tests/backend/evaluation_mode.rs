//! Values the definition leaves to the implementation are computed only inside an execution.
//!
//! `keys_list`, `values` and `Set2List` of two or more items list them in an order domains.md does
//! not fix. Outside an execution (`EvaluationMode::Proof`, the mode when no execution or search is
//! running) such an application stays unevaluated, as a defined value; inside one it is the
//! listing in k-rust's order. With zero or one item every listing is the same, so it is evaluated
//! in every mode.

use k_rust_backend::{
    builtin::BuiltinEffect,
    definition::BackendDefinition,
    diagnostic::{self, BackendDiagnostic},
    evaluation::{EvaluationMode, current, with_evaluation},
    rewrite::{ExecutionOptions, Pattern, execute_with_solver_and_observer},
    rule::Predicate,
    search::{SearchOptions, SearchType, search_graph_with_solver_and_observer},
    simplify::SimplificationOptions,
    smt::NoSolver,
    term::{Term, TermKind},
};
use k_rust_kore::kore::parser::parse_definition;

use crate::support::{internal_term, unstopped};

const FIXTURE: &str = r#"[]
module MAIN
  sort SortK{} []
  sort SortKItem{} []
  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
  sort SortString{} [hasDomainValues{}()]
  symbol inj{From, To}(From) : To [sortInjection{}()]
  axiom{R} \exists{R}(Value:SortKItem{},
      \equals{SortKItem{}, R}(Value:SortKItem{}, inj{SortInt{}, SortKItem{}}(From:SortInt{})))
      [subsort{SortInt{}, SortKItem{}}()]

  hooked-sort SortList{}
    [hook{}("LIST.List"), unit{}(Lbl'Stop'List{}()), element{}(LblListItem{}()),
     concat{}(Lbl'Unds'List'Unds'{}())]
  hooked-symbol Lbl'Stop'List{}() : SortList{} [function{}(), total{}(), hook{}("LIST.unit")]
  hooked-symbol LblListItem{}(SortKItem{}) : SortList{}
    [function{}(), total{}(), hook{}("LIST.element")]
  hooked-symbol Lbl'Unds'List'Unds'{}(SortList{}, SortList{}) : SortList{}
    [function{}(), total{}(), hook{}("LIST.concat"), assoc{}()]

  hooked-sort SortSet{}
    [hook{}("SET.Set"), unit{}(Lbl'Stop'Set{}()), element{}(LblSetItem{}()),
     concat{}(Lbl'Unds'Set'Unds'{}())]
  hooked-symbol Lbl'Stop'Set{}() : SortSet{} [function{}(), total{}(), hook{}("SET.unit")]
  hooked-symbol LblSetItem{}(SortKItem{}) : SortSet{}
    [function{}(), total{}(), hook{}("SET.element")]
  hooked-symbol Lbl'Unds'Set'Unds'{}(SortSet{}, SortSet{}) : SortSet{}
    [function{}(), hook{}("SET.concat"), assoc{}(), comm{}(), idem{}()]

  hooked-sort SortMap{}
    [hook{}("MAP.Map"), unit{}(Lbl'Stop'Map{}()), element{}(Lbl'UndsPipe'-'-GT-Unds'{}()),
     concat{}(Lbl'Unds'Map'Unds'{}())]
  hooked-symbol Lbl'Stop'Map{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
  hooked-symbol Lbl'UndsPipe'-'-GT-Unds'{}(SortKItem{}, SortKItem{}) : SortMap{}
    [function{}(), total{}(), hook{}("MAP.element")]
  hooked-symbol Lbl'Unds'Map'Unds'{}(SortMap{}, SortMap{}) : SortMap{}
    [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]

  hooked-symbol keysList{}(SortMap{}) : SortList{} [function{}(), hook{}("MAP.keys_list")]
  hooked-symbol values{}(SortMap{}) : SortList{} [function{}(), hook{}("MAP.values")]
  hooked-symbol setToList{}(SortSet{}) : SortList{}
    [function{}(), total{}(), hook{}("SET.set2list")]

  symbol dotk{}() : SortK{} [constructor{}()]
  hooked-symbol log{}(SortString{}) : SortK{} [function{}(), total{}(), hook{}("IO.logString")]
endmodule []"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(FIXTURE).expect("evaluation mode fixture should parse");
    BackendDefinition::internalize(&syntax, "MAIN")
        .expect("evaluation mode fixture should internalize")
}

fn int(value: i64) -> String {
    format!(r#"inj{{SortInt{{}}, SortKItem{{}}}}(\dv{{SortInt{{}}}}("{value}"))"#)
}

/// The map binding each key to `key + 100`.
fn map(keys: &[i64]) -> String {
    keys.iter()
        .map(|key| {
            format!(
                "Lbl'UndsPipe'-'-GT-Unds'{{}}({}, {})",
                int(*key),
                int(key + 100)
            )
        })
        .reduce(|left, right| format!("Lbl'Unds'Map'Unds'{{}}({left}, {right})"))
        .unwrap_or_else(|| "Lbl'Stop'Map{}()".into())
}

fn set(elements: &[i64]) -> String {
    elements
        .iter()
        .map(|element| format!("LblSetItem{{}}({})", int(*element)))
        .reduce(|left, right| format!("Lbl'Unds'Set'Unds'{{}}({left}, {right})"))
        .unwrap_or_else(|| "Lbl'Stop'Set{}()".into())
}

/// Every listing application of the test: `keys_list`, `values` and `Set2List` over `items`.
fn listings(items: &[i64]) -> [String; 3] {
    [
        format!("keysList{{}}({})", map(items)),
        format!("values{{}}({})", map(items)),
        format!("setToList{{}}({})", set(items)),
    ]
}

/// The simplification of `source`, and the diagnostics it emitted.
fn simplified(definition: &BackendDefinition, source: &str) -> (Term, Vec<BackendDiagnostic>) {
    let term = internal_term(definition, source);
    let (result, diagnostics) = diagnostic::collect(|| {
        unstopped::simplify(definition, &term, SimplificationOptions::default())
    });
    (
        result.expect("a listing simplifies without an error").term,
        diagnostics,
    )
}

fn is_list(term: &Term) -> bool {
    matches!(term.kind(), TermKind::List { rest: None, .. })
}

/// Outside an execution, a listing of two or more items stays unevaluated, without the
/// unsupported-hook warning (the outcome is the documented one), while a listing of zero or one
/// item, which every order gives alike, is evaluated.
#[test]
fn a_listing_of_two_or_more_items_stays_unevaluated_outside_an_execution() {
    let definition = definition();
    assert_eq!(current(), EvaluationMode::Proof);
    for source in listings(&[10, 2, -1]) {
        let (term, diagnostics) = simplified(&definition, &source);
        assert_eq!(
            term,
            internal_term(&definition, &source),
            "{source}: {term:?}"
        );
        assert!(diagnostics.is_empty(), "{source}: {diagnostics:?}");
    }
    for items in [&[][..], &[7][..]] {
        for source in listings(items) {
            let (term, _) = simplified(&definition, &source);
            assert!(is_list(&term), "{source}: {term:?}");
        }
    }
}

/// Inside an execution every listing is evaluated, in k-rust's order: decimal text order for Int
/// keys.
#[test]
fn a_listing_is_evaluated_inside_an_execution() {
    let definition = definition();
    for source in listings(&[10, 2, -1]) {
        let (term, _) = with_evaluation(EvaluationMode::Execution, || {
            simplified(&definition, &source)
        });
        assert!(is_list(&term), "{source}: {term:?}");
    }
    let (keys, _) = with_evaluation(EvaluationMode::Execution, || {
        simplified(&definition, &listings(&[10, 2, -1])[0])
    });
    let expected = internal_term(
        &definition,
        &format!(
            "Lbl'Unds'List'Unds'{{}}(LblListItem{{}}({}), Lbl'Unds'List'Unds'{{}}(LblListItem{{}}({}), LblListItem{{}}({})))",
            int(-1),
            int(10),
            int(2)
        ),
    );
    assert_eq!(keys, expected);
}

/// A listing left unevaluated is a defined value: a closed map with distinct constructor-like
/// keys has a listing, so the `\ceil` of the partial `keys_list` and `values` holds.
#[test]
fn an_unevaluated_listing_is_defined() {
    let definition = definition();
    for source in listings(&[10, 2, -1]) {
        let predicate = Predicate::Ceil(internal_term(&definition, &source));
        let simplified = unstopped::simplify_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &NoSolver,
        )
        .expect("the definedness of a listing simplifies");
        assert_eq!(simplified, Predicate::True, "{source}");
    }
}

/// A request that does not say it runs a program evaluates only consequences of the definition.
#[test]
fn execution_and_search_options_default_to_proof() {
    assert_eq!(
        ExecutionOptions::default().evaluation,
        EvaluationMode::Proof
    );
    assert_eq!(SearchOptions::default().evaluation, EvaluationMode::Proof);
}

/// An effect observer is the caller's code, not part of the run: whatever it evaluates while an
/// execution or a search in `Execution` mode reports an effect is outside the execution, so a
/// listing of two or more items stays unevaluated there.
#[test]
fn an_effect_observer_evaluates_outside_the_execution() {
    let definition = definition();
    let listing = internal_term(&definition, &listings(&[10, 2, -1])[0]);
    let initial = Pattern {
        term: internal_term(&definition, r#"log{}(\dv{SortString{}}("effect"))"#),
        constraints: Vec::new(),
    };
    let observe = |modes: &mut Vec<(EvaluationMode, bool)>, effect: &BuiltinEffect| {
        assert_eq!(*effect, BuiltinEffect::UserLog("effect".into()));
        let evaluated =
            unstopped::simplify(&definition, &listing, SimplificationOptions::default())
                .expect("a listing simplifies")
                .term;
        modes.push((current(), is_list(&evaluated)));
    };

    let mut executed = Vec::new();
    let result = execute_with_solver_and_observer(
        &definition,
        initial.clone(),
        ExecutionOptions {
            evaluation: EvaluationMode::Execution,
            ..ExecutionOptions::default()
        },
        &NoSolver,
        |effect| observe(&mut executed, effect),
    );
    assert_eq!(result.effects.len(), 1, "{result:?}");
    assert_eq!(executed, [(EvaluationMode::Proof, false)]);

    let mut searched = Vec::new();
    search_graph_with_solver_and_observer(
        &definition,
        initial,
        SearchOptions {
            search_type: SearchType::Star,
            evaluation: EvaluationMode::Execution,
            ..SearchOptions::default()
        },
        &NoSolver,
        |effect| observe(&mut searched, effect),
    );
    assert!(!searched.is_empty());
    assert!(
        searched
            .iter()
            .all(|observed| *observed == (EvaluationMode::Proof, false)),
        "{searched:?}"
    );
    assert_eq!(current(), EvaluationMode::Proof);
}
