//! The guarding pass on hand-built conditions, each with its guarded condition written by hand
//! (R12 of NT-37's review): where the tests go, in which order, which an earlier conjunct or
//! test already states, and what a `let` binds.

use krs_ir::testing::{item, item_in, origin, package_with};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, GeneratedOperation, ItemKind, SemanticId,
    SentenceKind,
};
use krs_ir_levels::definedness::Sorts;
use krs_ir_levels::{
    IrTermKind, ListOperands, SemanticCondition, SemanticRule, SemanticRuleCondition,
    SemanticSortRef, SemanticTerm, SemanticVariable,
};

use super::guard_rule;

fn k_item() -> SemanticSortRef {
    SemanticSortRef::declared(item_in(
        package_with("KRS-FRAMEWORK", "krs", "0.1.0", "framework"),
        "syntax",
        "KItem",
        ItemKind::Sort,
    ))
}

fn sort(sort: BuiltinSort) -> SemanticSortRef {
    SemanticSortRef::Builtin(sort)
}

fn var(name: &str, of: SemanticSortRef) -> SemanticTerm {
    SemanticTerm::variable(
        origin(&format!("v.{name}")),
        of,
        SemanticId::new(name).unwrap(),
    )
}

fn lit(value: &str) -> SemanticTerm {
    SemanticTerm::token(origin(&format!("t.{value}")), sort(BuiltinSort::Int), value).unwrap()
}

fn apply(
    operation: BuiltinOperation,
    of: SemanticSortRef,
    args: Vec<SemanticTerm>,
) -> SemanticTerm {
    SemanticTerm::application(origin("app"), of, ApplicationRef::Builtin(operation), args)
}

fn boolean(operation: BuiltinOperation, args: Vec<SemanticTerm>) -> SemanticTerm {
    apply(operation, sort(BuiltinSort::Bool), args)
}

fn project(name: &str) -> SemanticTerm {
    let int = sort(BuiltinSort::Int);
    SemanticTerm::application(
        origin("project"),
        int.clone(),
        ApplicationRef::Generated(GeneratedOperation::SortProjection(int)),
        vec![var(name, k_item())],
    )
}

fn let_in(pattern: SemanticTerm, value: SemanticTerm, body: SemanticTerm) -> SemanticTerm {
    let binds = match pattern.kind() {
        IrTermKind::Variable { variable } => vec![variable.clone()],
        _ => pattern
            .children()
            .into_iter()
            .filter_map(|child| match child.kind() {
                IrTermKind::Variable { variable } => Some(variable.clone()),
                _ => None,
            })
            .collect(),
    };
    SemanticTerm::let_binding(
        origin("let"),
        body.sort().clone(),
        pattern,
        value,
        body,
        binds,
    )
}

/// The condition `requires` of the transition `A => A`, guarded, as K writes it.
fn guarded(requires: SemanticTerm) -> Result<String, String> {
    let variables = ["A", "L", "I", "D", "X~0", "R~1", "S~2"]
        .into_iter()
        .map(|name| SemanticVariable::new(SemanticId::new(name).unwrap(), k_item()))
        .collect();
    let rule = SemanticRule::new(
        origin("rule"),
        item("rules", "r", ItemKind::Rule),
        SentenceKind::Transition,
        variables,
        SemanticTerm::rewrite(
            origin("rewrite"),
            k_item(),
            var("A", k_item()),
            var("A", k_item()),
        )
        .unwrap(),
    )
    .unwrap()
    .with_requires(Some(SemanticCondition::Bool(SemanticRuleCondition::new(
        origin("requires"),
        requires,
    ))))
    .unwrap();
    let guarded =
        guard_rule(&rule, &Sorts::new(k_item(), [])).map_err(|error| error.to_string())?;
    let Some(SemanticCondition::Bool(condition)) = guarded.requires() else {
        unreachable!("the condition stays Bool")
    };
    Ok(render(condition.term()))
}

fn render(term: &SemanticTerm) -> String {
    let all = |terms: Vec<&SemanticTerm>| terms.into_iter().map(render).collect::<Vec<_>>();
    match term.kind() {
        IrTermKind::Variable { variable } => variable.as_str().to_owned(),
        IrTermKind::Token { value } => value.clone(),
        IrTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } => match operation.spec().k_notation {
            krs_ir::BuiltinOperationNotation::Mixfix { pieces } => {
                let arguments = all(arguments.iter().collect());
                let mut text = String::from("(");
                for (index, piece) in pieces.iter().enumerate() {
                    text.push_str(piece);
                    if let Some(argument) = arguments.get(index) {
                        text.push_str(argument);
                    }
                }
                text.push(')');
                text
            }
            krs_ir::BuiltinOperationNotation::Call { name } => {
                format!("{name}({})", all(arguments.iter().collect()).join(", "))
            }
        },
        IrTermKind::Application {
            application: ApplicationRef::Generated(operation),
            arguments,
            ..
        } => {
            let arguments = all(arguments.iter().collect()).join(", ");
            match operation {
                GeneratedOperation::SortPredicate(SemanticSortRef::Builtin(of)) => {
                    format!("is{of:?}({arguments})")
                }
                GeneratedOperation::SortProjection(SemanticSortRef::Builtin(of)) => {
                    format!("{{{arguments}}}:>{of:?}")
                }
                _ => "?".to_owned(),
            }
        }
        IrTermKind::Application {
            application: ApplicationRef::Declared(id),
            arguments,
            ..
        } => format!(
            "{}({})",
            id.item_name(),
            all(arguments.iter().collect()).join(", ")
        ),
        IrTermKind::List(operands) => format!(
            "list:{:?}({})",
            operands.operation(),
            all(operands.operands().collect()).join(", ")
        ),
        IrTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => format!(
            "(#let {} = {} #in {})",
            render(pattern),
            render(value),
            render(body)
        ),
        IrTermKind::Matches {
            subject, pattern, ..
        } => format!("({} :=K {})", render(pattern), render(subject)),
        _ => "?".to_owned(),
    }
}

/// An operation's operands are tested before it, in order: the list read's bounds and its
/// projection, then the divisor.
#[test]
fn a_construct_s_operands_are_tested_before_it() {
    let read = SemanticTerm::list(
        origin("read"),
        sort(BuiltinSort::Int),
        ListOperands::Get {
            list: var("L", sort(BuiltinSort::List)),
            index: var("I", sort(BuiltinSort::Int)),
        },
    );
    let quotient = apply(
        BuiltinOperation::IntTDiv,
        sort(BuiltinSort::Int),
        vec![read, var("D", sort(BuiltinSort::Int))],
    );
    expect_test::expect![[
        "((I <Int list:Size(L)) andThenBool (((0 -Int list:Size(L)) <=Int I) andThenBool (isInt(list:Get(L, I)) andThenBool ((D =/=Int 0) andThenBool ((list:Get(L, I) /Int D) >Int 0)))))"
    ]]
    .assert_eq(&guarded(boolean(BuiltinOperation::IntGreater, vec![quotient, lit("0")])).unwrap());
}

/// A test an earlier conjunct states, as written or as a bound that implies it, or that the
/// pass made for an earlier conjunct, is not made again.
#[test]
fn a_stated_test_is_not_made_again() {
    let d = || var("D", sort(BuiltinSort::Int));
    let quotient = || {
        apply(
            BuiltinOperation::IntTDiv,
            sort(BuiltinSort::Int),
            vec![lit("8"), d()],
        )
    };
    let and = |left, right| boolean(BuiltinOperation::BoolAndThen, vec![left, right]);
    expect_test::expect!["((D >Int 0) andThenBool ((8 /Int D) >Int 1))"].assert_eq(
        &guarded(and(
            boolean(BuiltinOperation::IntGreater, vec![d(), lit("0")]),
            boolean(BuiltinOperation::IntGreater, vec![quotient(), lit("1")]),
        ))
        .unwrap(),
    );
    expect_test::expect![
        "((isInt(A) andThenBool ({A}:>Int >Int 0)) andThenBool ({A}:>Int <Int 9))"
    ]
    .assert_eq(
        &guarded(and(
            boolean(BuiltinOperation::IntGreater, vec![project("A"), lit("0")]),
            boolean(BuiltinOperation::IntLess, vec![project("A"), lit("9")]),
        ))
        .unwrap(),
    );
}

/// A `let` block at a conjunct holds its body's tests inside it; one below a negation is read
/// with its value in its name's place, and one whose pattern is more than a name is refused
/// where a test before the conjunct would read what it binds.
#[test]
fn a_let_s_names_are_tested_inside_it_or_through_its_value() {
    let x = || var("X~0", k_item());
    let body = || boolean(BuiltinOperation::IntGreater, vec![project("X~0"), lit("0")]);
    expect_test::expect!["(#let X~0 = A #in (isInt(X~0) andThenBool ({X~0}:>Int >Int 0)))"]
        .assert_eq(&guarded(let_in(x(), var("A", k_item()), body())).unwrap());
    expect_test::expect!["(isInt(A) andThenBool (notBool (#let X~0 = A #in ({X~0}:>Int >Int 0))))"]
        .assert_eq(
            &guarded(boolean(
                BuiltinOperation::BoolNot,
                vec![let_in(x(), var("A", k_item()), body())],
            ))
            .unwrap(),
        );
    let record = SemanticTerm::application(
        origin("record"),
        k_item(),
        ApplicationRef::Declared(item("syntax", "pair", ItemKind::Constructor)),
        vec![x(), var("R~1", k_item())],
    );
    let refused = guarded(boolean(
        BuiltinOperation::BoolNot,
        vec![let_in(record, var("A", k_item()), body())],
    ))
    .unwrap_err();
    assert!(
        refused.contains("binds by a pattern other than one name"),
        "{refused}"
    );
}
