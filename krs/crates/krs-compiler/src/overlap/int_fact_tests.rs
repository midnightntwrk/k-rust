//! The guard procedure's Int facts (F2 amendment, clause 4): conjuncts that
//! fix bits of a term (`bitRangeInt(t, o, l) ==Int v`, `t &Int m ==Int v`),
//! its value (`t ==Int c`), or bounds on it (`c <=Int t`, `t <Int c`) state
//! facts about `t`, and two guards whose facts about one term cannot all hold
//! separate their rules. This is what keeps `k::bits!` templates that differ
//! in a fixed bit disjoint, whether the guard is the sugar's or written by
//! hand. Builtin Int operations on literals are evaluated, so a literal
//! subject meets a template's guard by value.

use std::collections::BTreeSet;

use krs_ir::{ApplicationRef, BuiltinOperation, BuiltinSort, ItemKind, PackageId, StableItemId};
use krs_ir_levels::SemanticSortRef;

use super::{Pattern, SortGraph, Unifier, VariableKey};

use BuiltinOperation::{
    BoolAndThen, IntAdd, IntBitAnd, IntBitRange, IntEqual, IntGreaterEqual, IntLess, IntLessEqual,
    IntNotEqual, IntShiftRight,
};

fn constructor_id(name: &str) -> StableItemId {
    StableItemId::new(
        PackageId::new("FACTS", "facts", "0.1.0", "test").unwrap(),
        ["fixture"],
        name,
        ItemKind::Constructor,
        "",
    )
    .unwrap()
}

fn graph() -> SortGraph {
    let mut graph = SortGraph {
        candidates: BuiltinSort::ALL
            .into_iter()
            .map(SemanticSortRef::Builtin)
            .collect::<BTreeSet<_>>(),
        free_constructors: ["Decode"].into_iter().map(constructor_id).collect(),
        ..SortGraph::default()
    };
    graph.build_closure();
    graph
}

fn variable(rule: usize) -> Pattern {
    Pattern::Variable {
        key: VariableKey { rule, ordinal: 0 },
        sort: SemanticSortRef::Builtin(BuiltinSort::Int),
    }
}

fn int(value: i128) -> Pattern {
    Pattern::Token {
        sort: SemanticSortRef::Builtin(BuiltinSort::Int),
        value: value.to_string(),
    }
}

fn builtin(operation: BuiltinOperation, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        instance: Vec::new(),
        sort: SemanticSortRef::Builtin(operation.result_sort().builtin().unwrap()),
        application: ApplicationRef::Builtin(operation),
        arguments,
    }
}

fn decode(argument: Pattern) -> Pattern {
    Pattern::Application {
        instance: Vec::new(),
        sort: SemanticSortRef::Builtin(BuiltinSort::KSequence),
        application: ApplicationRef::Declared(constructor_id("Decode")),
        arguments: vec![argument],
    }
}

fn all(conjuncts: Vec<Pattern>) -> Pattern {
    conjuncts
        .into_iter()
        .reduce(|left, right| builtin(BoolAndThen, vec![left, right]))
        .unwrap()
}

/// The guard `k::bits!(template)` stands for, over the variable of `rule`:
/// the range, then one `bitRangeInt` equality per maximal fixed run of each
/// space-separated group.
fn template(rule: usize, text: &str) -> Pattern {
    let bits = text.chars().filter(|character| *character != ' ').count();
    let width = u32::try_from(bits).unwrap();
    let mut conjuncts = vec![
        builtin(IntGreaterEqual, vec![variable(rule), int(0)]),
        builtin(IntLess, vec![variable(rule), int(1 << width)]),
    ];
    let mut position = width;
    for group in text.split(' ') {
        let mut run: Option<(u32, i128, u32)> = None;
        let flush = |run: &mut Option<(u32, i128, u32)>, conjuncts: &mut Vec<Pattern>| {
            if let Some((offset, value, length)) = run.take() {
                conjuncts.push(builtin(
                    IntEqual,
                    vec![
                        builtin(
                            IntBitRange,
                            vec![variable(rule), int(offset.into()), int(length.into())],
                        ),
                        int(value),
                    ],
                ));
            }
        };
        for character in group.chars() {
            position -= 1;
            match character {
                '0' | '1' => {
                    let bit = i128::from(character == '1');
                    run = Some(match run {
                        Some((_, value, length)) => (position, value * 2 + bit, length + 1),
                        None => (position, bit, 1),
                    });
                }
                _ => flush(&mut run, &mut conjuncts),
            }
        }
        flush(&mut run, &mut conjuncts);
    }
    all(conjuncts)
}

/// Whether the rules `Decode(X0) requires left` and `Decode(right_subject)
/// requires right` are separated by their guards.
fn separated(left: &Pattern, right_subject: Pattern, right: Option<&Pattern>) -> bool {
    let graph = graph();
    let mut unifier = Unifier::new(&graph);
    assert!(unifier.unify(decode(variable(0)), decode(right_subject)));
    unifier.guards_separate(Some(left), right)
}

fn templates_separated(left: &str, right: &str) -> bool {
    let forward = separated(&template(0, left), variable(1), Some(&template(1, right)));
    let backward = separated(&template(0, right), variable(1), Some(&template(1, left)));
    assert_eq!(forward, backward, "{left} / {right}");
    forward
}

#[test]
fn templates_differing_in_a_fixed_bit_are_disjoint() {
    // The SM83 grid: the same runs with different values.
    assert!(templates_separated("00 yyy 100", "00 yyy 101"));
    assert!(templates_separated("00 pp0 001", "00 pp1 001"));
    assert!(templates_separated("00 yyy zzz", "01 yyy zzz"));
    // Different runs that disagree on one bit.
    assert!(templates_separated("00 1cc 000", "00 pp0 001"));
    assert!(templates_separated("0011 __01", "____ _1_0"));
    // Templates that share a value overlap.
    assert!(!templates_separated("00 yyy 100", "00 1cc 100"));
    assert!(!templates_separated("01 yyy zzz", "01 110 110"));
    assert!(!templates_separated("____", "1___"));
}

#[test]
fn templates_of_different_widths_meet_only_below_the_narrower_bound() {
    // `1_` matches 2 and 3; `0__1` matches only odd numbers below 8.
    assert!(!templates_separated("1_", "0__1"));
    // `1___` matches 8 to 15, never below 4.
    assert!(templates_separated("1___", "__"));
}

#[test]
fn a_literal_subject_meets_a_template_by_value() {
    let ld = template(0, "01 yyy zzz");
    assert!(!separated(&ld, int(65), None));
    assert!(separated(&ld, int(4), None));
    assert!(separated(&ld, int(256 + 65), None));
    assert!(separated(&ld, int(-1), None));
    // The authored `op =/=Int 118` beside the template excludes HALT.
    let ld_not_halt = all(vec![
        builtin(IntNotEqual, vec![variable(0), int(118)]),
        template(0, "01 yyy zzz"),
    ]);
    assert!(separated(&ld_not_halt, int(118), None));
}

#[test]
fn hand_written_mask_and_value_guards_are_read_alike() {
    // `x &Int 199 ==Int 4` (`00 yyy 100`) against `x &Int 199 ==Int 5`.
    let mask = |rule: usize, value: i128| {
        builtin(
            IntEqual,
            vec![
                builtin(IntBitAnd, vec![variable(rule), int(199)]),
                int(value),
            ],
        )
    };
    assert!(separated(&mask(0, 4), variable(1), Some(&mask(1, 5))));
    assert!(!separated(&mask(0, 4), variable(1), Some(&mask(1, 4))));
    // A mask against a template: `0xC7 & x == 4` is `00 yyy 100`.
    assert!(separated(
        &mask(0, 4),
        variable(1),
        Some(&template(1, "00 yyy 101"))
    ));
    // A value outside the mask makes the conjunct false.
    assert!(separated(&mask(0, 8), variable(1), None));
}

#[test]
fn equalities_and_bounds_of_one_term_meet_or_not() {
    let field = |rule: usize| builtin(IntShiftRight, vec![variable(rule), int(6)]);
    let equals = |rule: usize, value: i128| builtin(IntEqual, vec![field(rule), int(value)]);
    // The hand-written `FieldX(op) == 0` against `FieldX(op) == 3`.
    assert!(separated(&equals(0, 0), variable(1), Some(&equals(1, 3))));
    assert!(!separated(&equals(0, 3), variable(1), Some(&equals(1, 3))));
    let at_least =
        |rule: usize, bound: i128| builtin(IntLessEqual, vec![int(bound), variable(rule)]);
    let below = |rule: usize, bound: i128| builtin(IntLess, vec![variable(rule), int(bound)]);
    assert!(separated(
        &at_least(0, 10),
        variable(1),
        Some(&below(1, 10))
    ));
    assert!(!separated(
        &at_least(0, 10),
        variable(1),
        Some(&below(1, 11))
    ));
    // Nothing is known of a term compared with another term.
    let sum = builtin(IntAdd, vec![variable(1), int(1)]);
    assert!(!separated(&at_least(0, 10), sum, Some(&below(1, 5))));
}
