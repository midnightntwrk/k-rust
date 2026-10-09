//! Function contexts (K's `[[ .. ]]`, KF-025): an equation may end with a
//! `k::cells! { cell: .., .. }: Machine` parameter that reads the
//! configuration. Its binders join the binder list after the subject's, its
//! cells continue the left-hand provenance ordinals, and it is rejected on
//! every other sentence.

use krs_syntax::{
    KrsSyntax, ProvenanceRole, RuleItem, StateRuleBindingKind, SyntaxError, SyntaxErrorKind,
};

const ONLY_ON_EQUATIONS: &str =
    "a configuration context belongs only on #[k::equation] (K's [[ ]] function context)";
const SHAPE: &str = "a function context is a final `k::cells! { cell: .., .. }` parameter typed by the configuration struct";
const REMAINDER: &str =
    "a function context frames the rest of the configuration with an anonymous `..`";

fn context_reason(error: &SyntaxError) -> String {
    match error.kind() {
        SyntaxErrorKind::InvalidFunctionContext { reason } => reason.clone(),
        other => panic!("expected an invalid-function-context error, found {other:?}: {error}"),
    }
}

fn binder_reason(error: &SyntaxError) -> String {
    match error.kind() {
        SyntaxErrorKind::InvalidBinderList { reason } => reason.clone(),
        other => panic!("expected an invalid-binder-list error, found {other:?}: {error}"),
    }
}

const BAR_PLUS: &str = "fn bar_plus(
    n: Term<Int>,
    b: Term<Int>,
    k::term![BarPlus(n)]: Term<Int>,
    k::cells! {
        bar: k::configuration::Cell(b),
        baz: k::configuration::Cell(0),
        ..
    }: Machine,
) -> Term<Int> {
    int::add(b, n)
}";

#[test]
fn a_two_cell_context_declares_its_binders_after_the_subject() {
    let rule = RuleItem::parse_equation_source(BAR_PLUS).unwrap();
    let context = rule.function_context().expect("a function context");
    assert_eq!(context.pattern().entries().len(), 2);
    let names = context
        .bindings()
        .iter()
        .map(|binding| (binding.name().to_string(), binding.kind()))
        .collect::<Vec<_>>();
    assert_eq!(names, [("b".to_owned(), StateRuleBindingKind::Term)]);
    assert_eq!(
        context.bindings()[0]
            .term_sort()
            .map(krs_syntax::TermSort::sort_token_text),
        Some("Int".to_owned())
    );
    // The result and the condition see the context's binders.
    let names = rule
        .condition_bindings()
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    assert_eq!(names, ["n", "b"]);
}

#[test]
fn context_cells_continue_the_subjects_left_hand_ordinals() {
    let rule = RuleItem::parse_equation_source(BAR_PLUS).unwrap();
    let anchors = rule.full_provenance().unwrap();
    let ordinals = |role: ProvenanceRole| {
        let mut ordinals = anchors
            .iter()
            .filter(|anchor| anchor.role() == role)
            .map(krs_syntax::ProvenanceAnchor::ordinal)
            .collect::<Vec<_>>();
        ordinals.sort_unstable();
        ordinals
    };
    // `BarPlus(n)`: one head and one reference; the context adds `b` and `0`.
    assert_eq!(ordinals(ProvenanceRole::RuleLeftApplicationHead), [0]);
    assert_eq!(ordinals(ProvenanceRole::RuleLeftReference), [0, 1]);
    assert_eq!(ordinals(ProvenanceRole::RuleLeftLiteral), [0]);
    assert_eq!(ordinals(ProvenanceRole::FunctionContext), [0]);
    assert_eq!(ordinals(ProvenanceRole::FunctionContextType), [0]);
    assert_eq!(ordinals(ProvenanceRole::RuleLeftCellsField), [0, 1]);
    assert_eq!(ordinals(ProvenanceRole::RuleLeftCellsWrapper), [0, 1]);
}

#[test]
fn a_one_cell_context_may_frame_the_computation_cell() {
    let rule = RuleItem::parse_equation_source(
        "fn peek(
            item: KItem,
            k::term![Peek()]: Term<KItem>,
            k::cells! { k: k::configuration::KCell(item, ..), .. }: Machine,
        ) -> Term<KItem> {
            item
        }",
    )
    .unwrap();
    let context = rule.function_context().unwrap();
    assert_eq!(context.pattern().entries().len(), 1);
    assert_eq!(context.bindings()[0].name().to_string(), "item");
}

#[test]
fn a_context_without_an_anonymous_remainder_is_rejected() {
    for context in [
        "k::cells! { bar: k::configuration::Cell(b) }: Machine",
        "k::cells! { bar: k::configuration::Cell(b), state @ .. }: Machine",
    ] {
        let error = RuleItem::parse_equation_source(&format!(
            "fn f(b: Term<Int>, k::term![F()]: Term<Int>, {context}) -> Term<Int> {{ b }}"
        ))
        .unwrap_err();
        assert_eq!(context_reason(&error), REMAINDER);
    }
}

#[test]
fn a_context_on_another_sentence_is_rejected() {
    let error = RuleItem::parse_source(BAR_PLUS).unwrap_err();
    assert_eq!(context_reason(&error), ONLY_ON_EQUATIONS);
}

#[test]
fn a_context_that_is_not_cells_is_rejected() {
    let error = RuleItem::parse_equation_source(
        "fn f(n: Term<Int>, k::term![F(n)]: Term<Int>, machine: Machine) -> Term<Int> { n }",
    )
    .unwrap_err();
    assert_eq!(context_reason(&error), SHAPE);
}

#[test]
fn the_binder_list_is_mandatory_and_exhaustive_with_a_context() {
    for (binders, expected) in [
        ("", "here `n, b`"),
        ("n: Term<Int>,", "here `n, b`"),
        ("b: Term<Int>, n: Term<Int>,", "here `n, b`"),
    ] {
        let error = RuleItem::parse_equation_source(&format!(
            "fn f({binders} k::term![F(n)]: Term<Int>, \
             k::cells! {{ bar: k::configuration::Cell(b), .. }}: Machine) -> Term<Int> {{ b }}"
        ))
        .unwrap_err();
        let reason = binder_reason(&error);
        assert!(reason.contains(expected), "{reason}");
    }
    let error = RuleItem::parse_equation_source(
        "fn f(n: Term<Int>, b: Term<Int>, c: Term<Int>, k::term![F(n)]: Term<Int>, \
         k::cells! { bar: k::configuration::Cell(b), .. }: Machine) -> Term<Int> { b }",
    )
    .unwrap_err();
    assert_eq!(
        binder_reason(&error),
        "binder `c` is declared but does not occur in the subject or function context"
    );
}

#[test]
fn a_context_binder_shared_with_the_subject_is_declared_once() {
    let rule = RuleItem::parse_equation_source(
        "fn f(n: Term<Int>, k::term![F(n)]: Term<Int>, \
         k::cells! { bar: k::configuration::Cell(n), .. }: Machine) -> Term<Int> { n }",
    )
    .unwrap();
    assert_eq!(rule.binders().len(), 1);
    assert_eq!(rule.condition_bindings().len(), 1);
}
