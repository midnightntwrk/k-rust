//! The tests of each partial construct, pinned by hand (R12 of NT-37's review): a wrong test,
//! a missing fact or a fact stated for a total operation fails here, where the check, which
//! shares [`super::requirements`] with the guarding pass, cannot see it.

use krs_ir::testing::{item, item_in, origin, package_with};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, GeneratedOperation, ItemKind, SemanticId,
    SentenceKind,
};

use super::{
    NotShown, Place, Requirement, Sorts, dead_tests, requirements, unguarded, without_value,
};
use crate::{
    IrTermKind, ListOperands, MapOperands, SemanticCondition, SemanticRule, SemanticRuleCondition,
    SemanticSortRef, SemanticTerm, SemanticVariable, SetOperands,
};

fn k_item() -> SemanticSortRef {
    SemanticSortRef::declared(item_in(
        package_with("KRS-FRAMEWORK", "krs", "0.1.0", "framework"),
        "syntax",
        "KItem",
        ItemKind::Sort,
    ))
}

fn builtin_sort(sort: BuiltinSort) -> SemanticSortRef {
    SemanticSortRef::Builtin(sort)
}

fn int() -> SemanticSortRef {
    builtin_sort(BuiltinSort::Int)
}

fn bool_sort() -> SemanticSortRef {
    builtin_sort(BuiltinSort::Bool)
}

fn pair_sort() -> SemanticSortRef {
    SemanticSortRef::declared(item("syntax", "Pair", ItemKind::Sort))
}

fn pair_constructor() -> krs_ir::StableItemId {
    item("syntax", "pair", ItemKind::Constructor)
}

fn sorts() -> Sorts {
    Sorts::new(k_item(), [])
}

/// The sorts with `Pair`, whose values are `pair(Int, Int)`'s.
fn record_sorts() -> Sorts {
    let mut sorts = sorts();
    sorts
        .records
        .insert(pair_sort(), (pair_constructor(), vec![int(), int()]));
    sorts
}

fn var(name: &str, sort: SemanticSortRef) -> SemanticTerm {
    SemanticTerm::variable(
        origin(&format!("v.{name}")),
        sort,
        SemanticId::new(name).unwrap(),
    )
}

fn lit(value: &str) -> SemanticTerm {
    SemanticTerm::token(origin(&format!("t.{value}")), int(), value).unwrap()
}

fn apply(
    operation: BuiltinOperation,
    sort: SemanticSortRef,
    args: Vec<SemanticTerm>,
) -> SemanticTerm {
    SemanticTerm::application(
        origin("app"),
        sort,
        ApplicationRef::Builtin(operation),
        args,
    )
}

fn generated(
    operation: GeneratedOperation<SemanticSortRef>,
    sort: SemanticSortRef,
    operand: SemanticTerm,
) -> SemanticTerm {
    SemanticTerm::application(
        origin("generated"),
        sort,
        ApplicationRef::Generated(operation),
        vec![operand],
    )
}

fn list(operands: ListOperands<SemanticTerm>, sort: SemanticSortRef) -> SemanticTerm {
    SemanticTerm::list(origin("list"), sort, operands)
}

/// A term as K writes it, enough to tell the tests apart: an operation by its K label's
/// spelling, a sort test `isS(..)`, a name with its sort when that is `KItem`.
fn render(term: &SemanticTerm) -> String {
    let all = |terms: Vec<&SemanticTerm>| terms.into_iter().map(render).collect::<Vec<_>>();
    match term.kind() {
        IrTermKind::Variable { variable }
            if variable.kind() == krs_ir::SemanticIdKind::Wildcard =>
        {
            "_".to_owned()
        }
        IrTermKind::Variable { variable } if *term.sort() == k_item() => {
            format!("{}:KItem", variable.as_str())
        }
        IrTermKind::Variable { variable } => variable.as_str().to_owned(),
        IrTermKind::Token { value } => value.clone(),
        IrTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } => {
            let arguments = all(arguments.iter().collect());
            match operation.spec().k_notation {
                krs_ir::BuiltinOperationNotation::Mixfix { pieces } => {
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
                    format!("{name}({})", arguments.join(", "))
                }
            }
        }
        IrTermKind::Application {
            application: ApplicationRef::Generated(GeneratedOperation::SortPredicate(sort)),
            arguments,
            ..
        } => format!(
            "is{}({})",
            sort_name(sort),
            all(arguments.iter().collect()).join(", ")
        ),
        IrTermKind::Application {
            application: ApplicationRef::Declared(id),
            arguments,
            ..
        } => format!(
            "{}({})",
            id.item_name(),
            all(arguments.iter().collect()).join(", ")
        ),
        IrTermKind::Map(operands) => {
            format!(
                "map:{:?}({})",
                operands.operation(),
                all(operands.operands().collect()).join(", ")
            )
        }
        IrTermKind::List(operands) => {
            format!(
                "list:{:?}({})",
                operands.operation(),
                all(operands.operands().collect()).join(", ")
            )
        }
        IrTermKind::Set(operands) => {
            format!(
                "set:{:?}({})",
                operands.operation(),
                all(operands.operands().collect()).join(", ")
            )
        }
        IrTermKind::Matches {
            subject, pattern, ..
        } => format!("({} :=K {})", render(pattern), render(subject)),
        _ => "?".to_owned(),
    }
}

fn sort_name(sort: &SemanticSortRef) -> String {
    match sort {
        SemanticSortRef::Builtin(sort) => format!("{sort:?}"),
        SemanticSortRef::Declared(id) => id.item_name().to_owned(),
        _ => "?".to_owned(),
    }
}

fn tests_of(term: &SemanticTerm, sorts: &Sorts) -> Vec<String> {
    let mut wildcards = 0;
    requirements(term, true, sorts)
        .iter()
        .map(|requirement| {
            render(&requirement.test(
                sorts,
                &mut krs_ir::NodeOrigin::clone,
                &mut krs_ir::NodeOrigin::clone,
                &mut |_, typed| {
                    wildcards += 1;
                    super::test_name(typed, wildcards)
                },
            ))
        })
        .collect()
}

/// The operands the cases below read: `X`, `Y`, `Z` Ints, a list `L`, a map `M`, bytes `B` and a
/// string `S`.
struct Operands {
    first: SemanticTerm,
    second: SemanticTerm,
    third: SemanticTerm,
    list: SemanticTerm,
    map: SemanticTerm,
    bytes: SemanticTerm,
    text: SemanticTerm,
}

fn operands() -> Operands {
    Operands {
        first: var("X", int()),
        second: var("Y", int()),
        third: var("Z", int()),
        list: var("L", builtin_sort(BuiltinSort::List)),
        map: var("M", builtin_sort(BuiltinSort::Map)),
        bytes: var("B", builtin_sort(BuiltinSort::Bytes)),
        text: var("S", builtin_sort(BuiltinSort::String)),
    }
}

fn assert_tests(cases: Vec<(SemanticTerm, &[&str])>) {
    let sorts = sorts();
    for (term, expected) in cases {
        assert_eq!(tests_of(&term, &sorts), expected, "{}", render(&term));
    }
}

/// A projection, a lookup, a list's reads and updates, and a set concatenation.
#[test]
fn a_projection_and_a_collection_operation_have_the_tests_their_domains_state() {
    let Operands {
        first,
        second,
        list: items,
        map: env,
        ..
    } = operands();
    let projection = generated(
        GeneratedOperation::SortProjection(int()),
        int(),
        var("A", k_item()),
    );
    let read = |index: SemanticTerm, sort: SemanticSortRef| {
        list(
            ListOperands::Get {
                list: items.clone(),
                index,
            },
            sort,
        )
    };
    assert_tests(vec![
        (projection, &["isInt(A:KItem)"]),
        (
            SemanticTerm::typed_map(
                origin("get"),
                bool_sort(),
                MapOperands::Get {
                    map: env.clone(),
                    key: first.clone(),
                },
            ),
            &["map:InKeys(X, M)", "isBool(map:Get(M, X))"],
        ),
        (
            SemanticTerm::typed_map(
                origin("get"),
                k_item(),
                MapOperands::GetOrDefault {
                    map: env.clone(),
                    key: first.clone(),
                    default: second.clone(),
                },
            ),
            &[],
        ),
        (
            read(first.clone(), int()),
            &[
                "(X <Int list:Size(L))",
                "((0 -Int list:Size(L)) <=Int X)",
                "isInt(list:Get(L, X))",
            ],
        ),
        // A natural literal is after the start, a negative one before the end.
        (read(lit("0"), k_item()), &["(0 <Int list:Size(L))"]),
        (
            read(lit("-1"), k_item()),
            &["((0 -Int list:Size(L)) <=Int -1)"],
        ),
    ]);
}

/// A list's updates and a set concatenation.
#[test]
fn a_collection_update_has_the_tests_its_domain_states() {
    let Operands {
        first,
        second,
        list: items,
        ..
    } = operands();
    assert_tests(vec![
        (
            list(
                ListOperands::Update {
                    list: items.clone(),
                    index: first.clone(),
                    value: second.clone(),
                },
                builtin_sort(BuiltinSort::List),
            ),
            &["(X <Int list:Size(L))", "(0 <=Int X)"],
        ),
        (
            list(
                ListOperands::Make {
                    length: first.clone(),
                    value: second.clone(),
                },
                builtin_sort(BuiltinSort::List),
            ),
            &["(0 <=Int X)"],
        ),
        (
            list(
                ListOperands::Range {
                    list: items.clone(),
                    from_front: first.clone(),
                    from_back: second.clone(),
                },
                builtin_sort(BuiltinSort::List),
            ),
            &[
                "(0 <=Int X)",
                "(0 <=Int Y)",
                "((X +Int Y) <=Int list:Size(L))",
            ],
        ),
        (
            list(
                ListOperands::UpdateAll {
                    list: items.clone(),
                    index: first.clone(),
                    replacement: var("R", builtin_sort(BuiltinSort::List)),
                },
                builtin_sort(BuiltinSort::List),
            ),
            &["(0 <=Int X)", "((X +Int list:Size(R)) <=Int list:Size(L))"],
        ),
        (
            SemanticTerm::set(
                origin("concat"),
                builtin_sort(BuiltinSort::Set),
                SetOperands::Concat {
                    left: var("S1", builtin_sort(BuiltinSort::Set)),
                    right: var("S2", builtin_sort(BuiltinSort::Set)),
                },
            ),
            &["(set:Intersect(S1, S2) ==K set:Empty())"],
        ),
    ]);
}

/// The Int operations whose domain the catalog states, and two total ones.
#[test]
fn an_int_operation_has_the_tests_its_domain_states() {
    let Operands {
        first,
        second,
        third,
        ..
    } = operands();
    assert_tests(vec![
        (
            apply(
                BuiltinOperation::IntTDiv,
                int(),
                vec![first.clone(), second.clone()],
            ),
            &["(Y =/=Int 0)"],
        ),
        (
            apply(
                BuiltinOperation::IntMod,
                int(),
                vec![first.clone(), lit("2")],
            ),
            &[],
        ),
        (
            apply(
                BuiltinOperation::IntMod,
                int(),
                vec![first.clone(), lit("0")],
            ),
            &["(0 =/=Int 0)"],
        ),
        (
            apply(
                BuiltinOperation::IntDivides,
                bool_sort(),
                vec![first.clone(), second.clone()],
            ),
            &["(X =/=Int 0)"],
        ),
        (
            apply(
                BuiltinOperation::IntShiftLeft,
                int(),
                vec![first.clone(), second.clone()],
            ),
            &["(0 <=Int Y)"],
        ),
        (
            apply(
                BuiltinOperation::IntPow,
                int(),
                vec![first.clone(), lit("3")],
            ),
            &[],
        ),
        (
            apply(
                BuiltinOperation::IntPowMod,
                int(),
                vec![first.clone(), second.clone(), third.clone()],
            ),
            &["(Z =/=Int 0)", "(0 <=Int Y)"],
        ),
        (
            apply(BuiltinOperation::IntLog2, int(), vec![first.clone()]),
            &["(0 <Int X)"],
        ),
        (
            apply(
                BuiltinOperation::IntSignExtendBitRange,
                int(),
                vec![first.clone(), second.clone(), third.clone()],
            ),
            &["(0 <=Int Y)", "(1 <=Int Z)"],
        ),
        (
            apply(
                BuiltinOperation::IntBitRange,
                int(),
                vec![first.clone(), lit("4"), lit("4")],
            ),
            &[],
        ),
    ]);
}

/// The Bytes and String operations whose domain the catalog states, and an untested one.
#[test]
fn a_bytes_or_string_operation_has_the_tests_its_domain_states() {
    let Operands {
        first,
        second,
        bytes,
        text,
        ..
    } = operands();
    assert_tests(vec![
        (
            apply(
                BuiltinOperation::BytesGet,
                int(),
                vec![bytes.clone(), first.clone()],
            ),
            &["(0 <=Int X)", "(X <Int lengthBytes(B))"],
        ),
        (
            apply(
                BuiltinOperation::BytesUpdate,
                builtin_sort(BuiltinSort::Bytes),
                vec![bytes.clone(), first.clone(), second.clone()],
            ),
            &[
                "(0 <=Int X)",
                "(X <Int lengthBytes(B))",
                "(0 <=Int Y)",
                "(Y <=Int 255)",
            ],
        ),
        (
            apply(
                BuiltinOperation::BytesReplaceAt,
                builtin_sort(BuiltinSort::Bytes),
                vec![
                    bytes.clone(),
                    first.clone(),
                    var("C", builtin_sort(BuiltinSort::Bytes)),
                ],
            ),
            &[
                "(0 <=Int X)",
                "((X +Int lengthBytes(C)) <=Int lengthBytes(B))",
            ],
        ),
        (
            apply(
                BuiltinOperation::StringSubstring,
                builtin_sort(BuiltinSort::String),
                vec![text.clone(), first.clone(), second.clone()],
            ),
            &["(0 <=Int X)", "(X <=Int Y)", "(Y <=Int lengthString(S))"],
        ),
        (
            apply(
                BuiltinOperation::StringFind,
                int(),
                vec![text.clone(), text.clone(), first.clone()],
            ),
            &["(0 <=Int X)", "(X <=Int lengthString(S))"],
        ),
        (
            apply(BuiltinOperation::StringOrd, int(), vec![text.clone()]),
            &["(lengthString(S) ==Int 1)"],
        ),
        (
            apply(
                BuiltinOperation::StringToBool,
                bool_sort(),
                vec![text.clone()],
            ),
            &["((S ==String \"true\") orElseBool (S ==String \"false\"))"],
        ),
        // Total, or untested: no test.
        (
            apply(
                BuiltinOperation::IntAdd,
                int(),
                vec![first.clone(), second.clone()],
            ),
            &[],
        ),
        (
            apply(BuiltinOperation::StringToInt, int(), vec![text.clone()]),
            &[],
        ),
        (
            apply(BuiltinOperation::BytesLength, int(), vec![bytes.clone()]),
            &[],
        ),
    ]);
}

/// A `let` statement is tested where its pattern may not match: a name of a sort below its
/// value's by its sort test; a record of a sort of other values too by matching, a name a field
/// gives its sort being a wildcard and any other an anonymous name of its sort; but not a name
/// of the value's sort or above, nor a record of names of a sort whose values are that record's.
#[test]
fn a_let_is_tested_where_its_pattern_may_not_match() {
    let value = var("V", pair_sort());
    let record = |first: SemanticSortRef| {
        SemanticTerm::application(
            origin("record"),
            pair_sort(),
            ApplicationRef::Declared(pair_constructor()),
            vec![var("X~0", first), var("Y~1", int())],
        )
    };
    let statement = |pattern: SemanticTerm| {
        SemanticTerm::let_binding(
            origin("let"),
            bool_sort(),
            pattern,
            value.clone(),
            SemanticTerm::token(origin("true"), bool_sort(), "true").unwrap(),
            Vec::new(),
        )
    };
    let mut fields = sorts();
    fields
        .fields
        .insert(pair_constructor(), vec![k_item(), int()]);
    assert_eq!(
        tests_of(&statement(record(k_item())), &fields),
        ["(pair(_, _) :=K V)"]
    );
    assert_eq!(
        tests_of(&statement(record(int())), &fields),
        ["(pair(_Krs_Defined__krs_1, _) :=K V)"]
    );
    let mut records = record_sorts();
    records.fields = fields.fields;
    assert_eq!(
        tests_of(&statement(record(int())), &records),
        Vec::<String>::new()
    );
    assert_eq!(
        tests_of(&statement(var("P~2", pair_sort())), &sorts()),
        Vec::<String>::new()
    );
    assert_eq!(
        tests_of(&statement(var("I~3", int())), &sorts()),
        ["isInt(V)"]
    );
}

/// An earlier conjunct states a fact when it is the test, or when its bounds of the operands by
/// constants decide it.
#[test]
fn an_earlier_bound_states_a_fact_it_implies() {
    let sorts = sorts();
    let w = var("W", int());
    let established = |fact: &SemanticTerm, construct: &SemanticTerm| {
        requirements(construct, true, &sorts)
            .iter()
            .all(|requirement| requirement.established_by(&[fact], &sorts))
    };
    let compare = |operation, left: SemanticTerm, right: SemanticTerm| {
        apply(operation, bool_sort(), vec![left, right])
    };
    let shift = apply(
        BuiltinOperation::IntShiftLeft,
        int(),
        vec![
            lit("1"),
            apply(BuiltinOperation::IntSub, int(), vec![w.clone(), lit("1")]),
        ],
    );
    assert!(established(
        &compare(BuiltinOperation::IntGreater, w.clone(), lit("0")),
        &shift
    ));
    assert!(!established(
        &compare(BuiltinOperation::IntGreaterEqual, w.clone(), lit("0")),
        &shift
    ));
    let division = apply(BuiltinOperation::IntTDiv, int(), vec![lit("8"), w.clone()]);
    assert!(established(
        &compare(BuiltinOperation::IntGreater, w.clone(), lit("0")),
        &division
    ));
    assert!(!established(
        &compare(BuiltinOperation::IntGreaterEqual, w.clone(), lit("0")),
        &division
    ));
    let negated = apply(
        BuiltinOperation::BoolNot,
        bool_sort(),
        vec![compare(BuiltinOperation::IntEqual, w.clone(), lit("0"))],
    );
    assert!(established(&negated, &division));
    let index = list(
        ListOperands::Get {
            list: var("L", builtin_sort(BuiltinSort::List)),
            index: w.clone(),
        },
        k_item(),
    );
    let lower = |requirement: &Requirement<'_>, fact: &SemanticTerm| {
        requirement.established_by(&[fact], &sorts)
    };
    let needed = requirements(&index, true, &sorts);
    assert!(lower(
        &needed[1],
        &compare(BuiltinOperation::IntLessEqual, lit("0"), w.clone())
    ));
    assert!(!lower(
        &needed[0],
        &compare(BuiltinOperation::IntLessEqual, lit("0"), w)
    ));
}

fn is_int(key: &str) -> SemanticTerm {
    SemanticTerm::application(
        origin(key),
        bool_sort(),
        ApplicationRef::Generated(GeneratedOperation::SortPredicate(int())),
        vec![var("A", k_item())],
    )
}

/// `{A}:>Int >Int 0`.
fn positive() -> SemanticTerm {
    apply(
        BuiltinOperation::IntGreater,
        bool_sort(),
        vec![
            generated(
                GeneratedOperation::SortProjection(int()),
                int(),
                var("A", k_item()),
            ),
            lit("0"),
        ],
    )
}

fn connective(operation: BuiltinOperation, operands: Vec<SemanticTerm>) -> SemanticTerm {
    apply(operation, bool_sort(), operands)
}

/// The transition `A => A` with condition `requires`, or `from => A` when `from` is given.
fn rule(requires: Option<SemanticTerm>, from: Option<SemanticTerm>) -> SemanticRule {
    let rewrite = SemanticTerm::rewrite(
        origin("rule.rewrite"),
        k_item(),
        from.unwrap_or_else(|| var("A", k_item())),
        var("A", k_item()),
    )
    .unwrap();
    SemanticRule::new(
        origin("rule"),
        item("rules", "r", ItemKind::Rule),
        SentenceKind::Transition,
        vec![SemanticVariable::new(
            SemanticId::new("A").unwrap(),
            k_item(),
        )],
        rewrite,
    )
    .unwrap()
    .with_requires(requires.map(|term| {
        SemanticCondition::Bool(SemanticRuleCondition::new(origin("rule.requires"), term))
    }))
    .unwrap()
}

fn check(rule: &SemanticRule) -> Option<Place> {
    unguarded(rule, &sorts()).map(|found| found.place)
}

#[test]
fn a_projection_in_a_condition_needs_its_test_before_it_at_a_conjunct() {
    use BuiltinOperation::{BoolAndThen, BoolNot, BoolOrElse};
    assert_eq!(check(&rule(Some(positive()), None)), Some(Place::Condition));
    let guarded = connective(BoolAndThen, vec![is_int("test"), positive()]);
    assert_eq!(check(&rule(Some(guarded), None)), None);
    // After the construct, the test comes too late.
    let late = connective(BoolAndThen, vec![positive(), is_int("test")]);
    assert_eq!(check(&rule(Some(late), None)), Some(Place::Condition));
    // Below a negation `false` makes the condition hold: the test there guards nothing.
    let negated = connective(
        BoolNot,
        vec![connective(BoolAndThen, vec![is_int("test"), positive()])],
    );
    assert_eq!(
        check(&rule(Some(negated.clone()), None)),
        Some(Place::Condition)
    );
    // The guarded form of the author's `!(is && proj)` and `!is || proj` passes the check, and
    // the author's test below `!` or `||` is reported as dead.
    for written in [
        negated,
        connective(
            BoolOrElse,
            vec![connective(BoolNot, vec![is_int("test")]), positive()],
        ),
    ] {
        let rule = rule(
            Some(connective(BoolAndThen, vec![is_int("guard"), written])),
            None,
        );
        assert_eq!(check(&rule), None);
        let dead = dead_tests(&rule, &sorts());
        assert_eq!(dead.len(), 1, "{dead:?}");
        assert_eq!(dead[0].test.key().as_str(), "test");
        assert_eq!(dead[0].name, "projection");
    }
    // A test before the construct in its chain is not dead.
    let guarded = rule(
        Some(connective(BoolAndThen, vec![is_int("test"), positive()])),
        None,
    );
    assert!(dead_tests(&guarded, &sorts()).is_empty());
}

#[test]
fn a_lookup_needs_its_key_and_its_projection_their_sort() {
    use BuiltinOperation::BoolAndThen;
    let map = || var("M", builtin_sort(BuiltinSort::Map));
    let read = |sort: SemanticSortRef| {
        SemanticTerm::typed_map(
            origin("read"),
            sort,
            MapOperands::Get {
                map: map(),
                key: var("A", k_item()),
            },
        )
    };
    assert_eq!(
        check(&rule(Some(read(bool_sort())), None)),
        Some(Place::Condition)
    );
    let in_keys = SemanticTerm::typed_map(
        origin("in-keys"),
        bool_sort(),
        MapOperands::InKeys {
            key: var("A", k_item()),
            map: map(),
        },
    );
    let is_bool = generated(
        GeneratedOperation::SortPredicate(bool_sort()),
        bool_sort(),
        read(k_item()),
    );
    let guarded = connective(
        BoolAndThen,
        vec![
            in_keys.clone(),
            connective(BoolAndThen, vec![is_bool, read(bool_sort())]),
        ],
    );
    assert_eq!(check(&rule(Some(guarded), None)), None);
    // The key alone leaves the projection to `Bool` untested.
    let half = connective(BoolAndThen, vec![in_keys, read(bool_sort())]);
    assert_eq!(check(&rule(Some(half), None)), Some(Place::Condition));
    // A pattern over evaluated terms evaluates the lookup before any condition.
    let wrapped = connective(
        BuiltinOperation::KEqualEq,
        vec![read(k_item()), var("A", k_item())],
    );
    assert_eq!(check(&rule(None, Some(wrapped))), Some(Place::Pattern));
    // A concatenation of sets there is matched, not built.
    let matched = SemanticTerm::set(
        origin("concat"),
        builtin_sort(BuiltinSort::Set),
        SetOperands::Concat {
            left: var("S1", builtin_sort(BuiltinSort::Set)),
            right: var("S2", builtin_sort(BuiltinSort::Set)),
        },
    );
    assert_eq!(check(&rule(None, Some(matched))), None);
}

/// What [`without_value`] reports of `result` built where `facts` hold: each construct with
/// `needs` for a fact not stated and `untested` for an operation no condition tests, then each
/// declared production applied.
fn not_shown(result: &SemanticTerm, facts: &[&SemanticTerm]) -> Vec<String> {
    let mut found = Vec::new();
    let mut applied = Vec::new();
    without_value(
        result,
        facts,
        &sorts(),
        &mut |construct, why| {
            found.push(match why {
                NotShown::Requirement(requirement) => format!(
                    "{} needs {}",
                    render(construct),
                    render(&requirement.test(
                        &sorts(),
                        &mut krs_ir::NodeOrigin::clone,
                        &mut krs_ir::NodeOrigin::clone,
                        &mut |_, typed| super::test_name(typed, 0),
                    ))
                ),
                NotShown::Untested(_) => format!("{} untested", render(construct)),
            });
        },
        &mut |_, production| applied.push(format!("applies {}", production.item_name())),
    );
    found.extend(applied);
    found
}

#[test]
fn a_result_s_construct_is_shown_by_the_fact_that_states_its_test() {
    let x = || var("X", int());
    let compare = |operation, left: SemanticTerm, right: SemanticTerm| {
        apply(operation, bool_sort(), vec![left, right])
    };
    let division = apply(BuiltinOperation::IntTDiv, int(), vec![lit("100"), x()]);
    assert_eq!(
        not_shown(&division, &[]),
        ["(100 /Int X) needs (X =/=Int 0)"]
    );
    let nonzero = compare(BuiltinOperation::IntNotEqual, x(), lit("0"));
    assert_eq!(not_shown(&division, &[&nonzero]), [""; 0]);
    // A bound that implies the fact shows it, and so does the negation an `if` block's second
    // equation states.
    let positive = compare(BuiltinOperation::IntGreater, x(), lit("0"));
    assert_eq!(not_shown(&division, &[&positive]), [""; 0]);
    let not_zero = apply(
        BuiltinOperation::BoolNot,
        bool_sort(),
        vec![compare(BuiltinOperation::IntEqual, x(), lit("0"))],
    );
    assert_eq!(not_shown(&division, &[&not_zero]), [""; 0]);
    // A construct below another operation is found, and one fact does not show another's.
    let shifted = apply(
        BuiltinOperation::IntAdd,
        int(),
        vec![
            apply(BuiltinOperation::IntShiftLeft, int(), vec![lit("1"), x()]),
            lit("1"),
        ],
    );
    assert_eq!(
        not_shown(&shifted, &[&nonzero]),
        ["(1 <<Int X) needs (0 <=Int X)"]
    );
}

#[test]
fn a_conditional_written_as_an_operation_guards_nothing() {
    let x = || var("X", int());
    let test = apply(
        BuiltinOperation::IntNotEqual,
        bool_sort(),
        vec![x(), lit("0")],
    );
    let conditional = apply(
        BuiltinOperation::KEqualIte,
        int(),
        vec![
            test,
            apply(BuiltinOperation::IntTDiv, int(), vec![lit("100"), x()]),
            lit("0"),
        ],
    );
    assert_eq!(
        not_shown(&conditional, &[]),
        ["(100 /Int X) needs (X =/=Int 0)"]
    );
}

#[test]
fn a_projected_read_in_a_result_needs_its_key_and_its_sort() {
    let map = || var("M", builtin_sort(BuiltinSort::Map));
    let read = |sort: SemanticSortRef| {
        SemanticTerm::typed_map(
            origin("read"),
            sort,
            MapOperands::Get {
                map: map(),
                key: lit("9"),
            },
        )
    };
    let in_keys = SemanticTerm::typed_map(
        origin("in-keys"),
        bool_sort(),
        MapOperands::InKeys {
            key: lit("9"),
            map: map(),
        },
    );
    let is_int = generated(
        GeneratedOperation::SortPredicate(int()),
        bool_sort(),
        read(k_item()),
    );
    assert_eq!(not_shown(&read(int()), &[]).len(), 2);
    // The key alone leaves the projection to `Int` unshown: nothing states that a typed map
    // holds its element sort.
    let half = not_shown(&read(int()), &[&in_keys]);
    assert_eq!(half.len(), 1, "{half:?}");
    assert!(half[0].contains("needs isInt("), "{half:?}");
    assert_eq!(not_shown(&read(int()), &[&in_keys, &is_int]), [""; 0]);
    // A read at `KItem` is K's own read: the key suffices.
    assert_eq!(not_shown(&read(k_item()), &[&in_keys]), [""; 0]);
    // A read with a default has every key, and is projected like any read.
    let or_default = |sort: SemanticSortRef| {
        SemanticTerm::typed_map(
            origin("read-or"),
            sort,
            MapOperands::GetOrDefault {
                map: map(),
                key: lit("9"),
                default: lit("0"),
            },
        )
    };
    assert_eq!(not_shown(&or_default(k_item()), &[]), [""; 0]);
    assert_eq!(not_shown(&or_default(int()), &[]).len(), 1);
}

#[test]
fn a_result_reports_untested_operations_applications_and_names_a_let_binds() {
    let text = var("S", builtin_sort(BuiltinSort::String));
    let parsed = apply(BuiltinOperation::StringToInt, int(), vec![text]);
    assert_eq!(not_shown(&parsed, &[]), ["String2Int(S) untested"]);
    let helper = item("syntax", "helper", ItemKind::Constructor);
    let called = SemanticTerm::application(
        origin("call"),
        int(),
        ApplicationRef::Declared(helper),
        vec![var("X", int())],
    );
    assert_eq!(not_shown(&called, &[]), ["applies helper"]);
    // A name bound alone is read with its value in its place, which a fact of the sentence
    // may state; a name a pattern binds is read by no condition of the sentence.
    let nonzero = |name: &str| {
        apply(
            BuiltinOperation::IntNotEqual,
            bool_sort(),
            vec![var(name, int()), lit("0")],
        )
    };
    let divide = |name: &str| {
        apply(
            BuiltinOperation::IntTDiv,
            int(),
            vec![lit("100"), var(name, int())],
        )
    };
    let bind = |pattern: SemanticTerm, value: SemanticTerm, body: SemanticTerm, binds: &[&str]| {
        SemanticTerm::let_binding(
            origin("let"),
            int(),
            pattern,
            value,
            body,
            binds
                .iter()
                .map(|name| SemanticId::new(*name).unwrap())
                .collect(),
        )
    };
    let named = bind(var("Y", int()), var("X", int()), divide("Y"), &["Y"]);
    assert_eq!(not_shown(&named, &[&nonzero("X")]), [""; 0]);
    let pair = SemanticTerm::application(
        origin("pair"),
        pair_sort(),
        ApplicationRef::Declared(pair_constructor()),
        vec![var("Y", int()), var("Z", int())],
    );
    let matched = bind(pair, var("P", k_item()), divide("Y"), &["Y", "Z"]);
    let found = not_shown(&matched, &[&nonzero("Y")]);
    assert_eq!(found.len(), 2, "{found:?}");
    assert_eq!(found[0], "(100 /Int Y) needs (Y =/=Int 0)");
    assert!(found[1].contains(":=K P:KItem"), "{found:?}");
}
