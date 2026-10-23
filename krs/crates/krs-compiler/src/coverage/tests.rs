//! Unit tests of the coverage lint: the pattern matrix over a hand-built
//! signature, and the guard decider against brute-force evaluation.

use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use krs_ir::{BuiltinSort, ItemKind, PackageId, StableItemId};
use krs_ir_levels::SemanticSortRef as Sort;
use krs_ir_levels::SortParameterId;
use num_bigint::BigInt;

use super::{
    Atom, Bound, Column, ConstructorInfo, Counterexample, Fact, Formula, Head, Order, Pattern,
    Projection, Projections, Row, Search, Signature, Verdict, decide, points, render,
};

const INT: Sort = Sort::Builtin(BuiltinSort::Int);
const BOOL: Sort = Sort::Builtin(BuiltinSort::Bool);
const STRING: Sort = Sort::Builtin(BuiltinSort::String);

fn package() -> PackageId {
    PackageId::new("COVERAGE", "coverage", "0.1.0", "test").unwrap()
}

fn sort(name: &str) -> Sort {
    Sort::Declared(StableItemId::new(package(), ["fixture"], name, ItemKind::Sort, "").unwrap())
}

/// A variant `family::name`, displayed `Family::Name`.
fn variant(family: &str, name: &str) -> StableItemId {
    StableItemId::new(
        package(),
        ["fixture"],
        name,
        ItemKind::Constructor,
        format!("{}{family}", krs_ir::ENUM_VARIANT_DISAMBIGUATOR_PREFIX),
    )
    .unwrap()
}

struct Builder {
    signature: Signature,
    parents: BTreeMap<Sort, BTreeSet<Sort>>,
}

impl Builder {
    fn new() -> Self {
        Self {
            signature: Signature {
                sorts: BuiltinSort::ALL.into_iter().map(Sort::Builtin).collect(),
                ..Signature::default()
            },
            parents: BTreeMap::new(),
        }
    }

    fn constructor(mut self, id: &StableItemId, result: Sort, arguments: &[Sort]) -> Self {
        self.signature.add_constructor(
            id.clone(),
            ConstructorInfo {
                result,
                parameters: Vec::new(),
                arguments: arguments.to_vec(),
            },
        );
        self
    }

    fn parametric(mut self, id: &StableItemId) -> Self {
        let parameter = SortParameterId::new("S");
        self.signature.add_constructor(
            id.clone(),
            ConstructorInfo {
                result: Sort::Parameter(parameter.clone()),
                parameters: vec![parameter.clone()],
                arguments: vec![Sort::Parameter(parameter)],
            },
        );
        self
    }

    fn subsort(mut self, below: Sort, above: Sort) -> Self {
        self.parents.entry(below).or_default().insert(above);
        self
    }

    fn build(mut self) -> Signature {
        let parents = std::mem::take(&mut self.parents);
        self.signature.close(&parents);
        self.signature
    }
}

fn binder(sort: Sort) -> Pattern {
    Pattern::Binder(sort)
}

fn construct(id: &StableItemId, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Constructor {
        id: id.clone(),
        instance: Vec::new(),
        arguments,
    }
}

fn int(value: i64) -> Pattern {
    Pattern::Literal {
        sort: INT,
        value: value.to_string(),
    }
}

fn boolean(value: bool) -> Pattern {
    Pattern::Literal {
        sort: BOOL,
        value: value.to_string(),
    }
}

fn row(patterns: Vec<Pattern>) -> Row {
    Row {
        patterns,
        guard: None,
    }
}

fn guarded(patterns: Vec<Pattern>, guard: Formula) -> Row {
    Row {
        patterns,
        guard: Some(Rc::new(guard)),
    }
}

fn columns(sorts: &[Sort]) -> Vec<Column> {
    sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| Column {
            sort: sort.clone(),
            path: vec![index],
            heads: None,
        })
        .collect()
}

/// The uncovered argument vectors, each rendered `(a, b)`.
fn gaps(signature: &Signature, rows: &[Row], sorts: &[Sort]) -> Vec<String> {
    let projections = Projections::new();
    let mut search = Search {
        signature,
        projections: &projections,
        ranges: &BTreeMap::new(),
        virtuals: &BTreeMap::new(),
        nodes: 0,
        valuations: 0,
        exhausted: false,
    };
    let found = search.missing(rows, &columns(sorts), &BTreeMap::new(), 3);
    assert!(!search.exhausted);
    found
        .iter()
        .map(|gap| {
            format!(
                "({})",
                gap.values.iter().map(render).collect::<Vec<_>>().join(", ")
            )
        })
        .collect()
}

fn bound(subject: &str, bound: Bound, constant: i64) -> Formula {
    Formula::Atom(Atom::Bound {
        subject: subject.to_owned(),
        bound,
        constant: BigInt::from(constant),
    })
}

fn opaque(key: &str) -> Formula {
    Formula::Atom(Atom::Opaque(key.to_owned()))
}

fn order(left: &str, right: &str, order: Order) -> Formula {
    Formula::Atom(Atom::Order {
        left: left.to_owned(),
        right: right.to_owned(),
        order,
    })
}

fn and(left: Formula, right: Formula) -> Formula {
    Formula::And(Box::new(left), Box::new(right))
}

fn or(left: Formula, right: Formula) -> Formula {
    Formula::Or(Box::new(left), Box::new(right))
}

#[test]
fn an_enum_is_covered_by_all_its_variants_and_names_the_missing_one() {
    let (a, b, c) = (
        variant("Register", "A"),
        variant("Register", "B"),
        variant("Register", "C"),
    );
    let register = sort("Reg");
    let signature = Builder::new()
        .constructor(&a, register.clone(), &[])
        .constructor(&b, register.clone(), &[])
        .constructor(&c, register.clone(), &[])
        .build();
    let all = [&a, &b, &c].map(|id| row(vec![construct(id, vec![])]));
    assert!(gaps(&signature, &all, std::slice::from_ref(&register)).is_empty());
    assert_eq!(
        gaps(&signature, &all[..2], std::slice::from_ref(&register)),
        ["(Register::C)"]
    );
    // A binder covers the rest; its sort decides what it covers.
    let rest = [
        row(vec![construct(&a, vec![])]),
        row(vec![binder(register.clone())]),
    ];
    assert!(gaps(&signature, &rest, &[register]).is_empty());
}

#[test]
fn a_constructor_is_decomposed_into_its_arguments() {
    let (pair, zero, one) = (
        variant("Value", "Pair"),
        variant("Bit", "Zero"),
        variant("Bit", "One"),
    );
    let (value, bit) = (sort("Value"), sort("Bit"));
    let signature = Builder::new()
        .constructor(&zero, bit.clone(), &[])
        .constructor(&one, bit.clone(), &[])
        .constructor(&pair, value.clone(), &[bit.clone(), bit.clone()])
        .build();
    let rows = [
        row(vec![
            construct(&pair, vec![construct(&zero, vec![]), binder(bit.clone())]),
            boolean(true),
        ]),
        row(vec![
            construct(
                &pair,
                vec![construct(&one, vec![]), construct(&zero, vec![])],
            ),
            binder(BOOL),
        ]),
    ];
    let mut found = gaps(&signature, &rows, &[value, BOOL]);
    found.sort();
    assert_eq!(
        found,
        [
            "(Value::Pair(Bit::One, Bit::One), false)",
            "(Value::Pair(Bit::One, Bit::One), true)",
            "(Value::Pair(Bit::Zero, Bit::Zero), false)",
        ]
    );
}

#[test]
fn a_subsort_injects_its_values_and_a_narrow_binder_covers_only_them() {
    let plus = variant("Exp", "Plus");
    let exp = sort("Exp");
    let signature = Builder::new()
        .constructor(&plus, exp.clone(), &[exp.clone(), exp.clone()])
        .subsort(INT, exp.clone())
        .build();
    let covered = [
        row(vec![construct(
            &plus,
            vec![binder(exp.clone()), binder(exp.clone())],
        )]),
        row(vec![binder(INT)]),
    ];
    assert!(gaps(&signature, &covered, std::slice::from_ref(&exp)).is_empty());
    // An Int binder in an Exp column misses Plus.
    assert_eq!(
        gaps(&signature, &covered[1..], std::slice::from_ref(&exp)),
        ["(Exp::Plus(_, _))"]
    );
    // Constructors alone miss the injected Ints; a witness is an Int.
    assert_eq!(gaps(&signature, &covered[..1], &[exp]), ["(0)"]);
}

#[test]
fn a_parametric_constructor_builds_values_of_every_declared_sort() {
    let (always, wrap) = (variant("Condition", "Always"), variant("Wrapper", "Wrap"));
    let condition = sort("Cond");
    let signature = Builder::new()
        .constructor(&always, condition.clone(), &[])
        .parametric(&wrap)
        .build();
    assert_eq!(
        gaps(
            &signature,
            &[row(vec![construct(&always, vec![])])],
            &[condition]
        ),
        ["(Wrapper::Wrap(_))"]
    );
}

#[test]
fn a_sort_no_constructor_builds_is_not_assumed_empty() {
    let opaque = sort("Abstract");
    let signature = Builder::new()
        .subsort(opaque.clone(), sort("Other"))
        .build();
    assert_eq!(gaps(&signature, &[], &[opaque]), ["(_)"]);
}

#[test]
fn literals_cover_only_themselves_except_bool() {
    let signature = Builder::new().build();
    let table = (0..8)
        .map(|index| row(vec![int(index)]))
        .collect::<Vec<_>>();
    assert_eq!(gaps(&signature, &table, &[INT]), ["(8)"]);
    let mut owise = table.clone();
    owise.push(row(vec![binder(INT)]));
    assert!(gaps(&signature, &owise, &[INT]).is_empty());
    let both = [row(vec![boolean(true)]), row(vec![boolean(false)])];
    assert!(gaps(&signature, &both, &[BOOL]).is_empty());
    assert_eq!(gaps(&signature, &both[..1], &[BOOL]), ["(false)"]);
    let empty = Pattern::Literal {
        sort: STRING,
        value: "\"\"".to_owned(),
    };
    assert_eq!(
        gaps(&signature, &[row(vec![empty])], &[STRING]),
        ["(\"1\")"]
    );
}

#[test]
fn an_opaque_pattern_covers_nothing() {
    let signature = Builder::new().build();
    assert_eq!(
        gaps(&signature, &[row(vec![Pattern::Opaque])], &[INT]),
        ["(0)"]
    );
}

#[test]
fn complementary_guards_cover_their_pattern() {
    let signature = Builder::new().build();
    let small = guarded(vec![binder(INT)], bound("$0", Bound::Below, 128));
    let large = guarded(vec![binder(INT)], bound("$0", Bound::Below, 128).not());
    assert!(gaps(&signature, &[small.clone(), large], &[INT]).is_empty());
    // One side alone leaves the other uncovered; the witness is the point.
    assert_eq!(gaps(&signature, &[small], &[INT]), ["(128)"]);
    // `x == true` and `x == false` read as a guard and its negation.
    let flag = guarded(vec![binder(BOOL)], opaque("$0"));
    let unset = guarded(vec![binder(BOOL)], opaque("$0").not());
    assert!(gaps(&signature, &[flag, unset], &[BOOL]).is_empty());
    // `a && b`, `!a`, and `a && !b` cover everything.
    let rows = [
        guarded(vec![binder(INT)], and(opaque("a"), opaque("b"))),
        guarded(vec![binder(INT)], opaque("a").not()),
        guarded(vec![binder(INT)], and(opaque("a"), opaque("b").not())),
    ];
    assert!(gaps(&signature, &rows, &[INT]).is_empty());
    assert_eq!(gaps(&signature, &rows[..2], &[INT]).len(), 1);
}

#[test]
fn guards_with_literal_rows_use_the_literals_as_facts() {
    // sgn(-1), sgn(x) when x < -1, when x == 0, when x > 0.
    let signature = Builder::new().build();
    let mut rows = vec![
        row(vec![int(-1)]),
        guarded(vec![binder(INT)], bound("$0", Bound::Below, -1)),
        guarded(vec![binder(INT)], bound("$0", Bound::At, 0)),
    ];
    assert_eq!(gaps(&signature, &rows, &[INT]), ["(1)"]);
    rows.push(guarded(vec![binder(INT)], bound("$0", Bound::Above, 0)));
    assert!(gaps(&signature, &rows, &[INT]).is_empty());
}

#[test]
fn guards_on_different_patterns_combine() {
    // drop(stack, n) when n <= 0; drop(Empty, n) and drop(Cons(_, _), n) when n > 0.
    let (empty, cons) = (variant("Stack", "Empty"), variant("Stack", "Cons"));
    let stack = sort("Stack");
    let signature = Builder::new()
        .constructor(&empty, stack.clone(), &[])
        .constructor(&cons, stack.clone(), &[INT, stack.clone()])
        .build();
    let positive = || bound("$1", Bound::Above, 0);
    let rows = [
        guarded(vec![binder(stack.clone()), binder(INT)], positive().not()),
        guarded(vec![construct(&empty, vec![]), binder(INT)], positive()),
        guarded(
            vec![
                construct(&cons, vec![binder(INT), binder(stack.clone())]),
                binder(INT),
            ],
            positive(),
        ),
    ];
    assert!(gaps(&signature, &rows, &[stack.clone(), INT]).is_empty());
    assert_eq!(
        gaps(&signature, &rows[..2], &[stack, INT]),
        ["(Stack::Cons(_, _), 1)"]
    );
}

#[test]
fn two_integers_are_in_exactly_one_order() {
    let signature = Builder::new().build();
    let rows = [
        guarded(
            vec![binder(INT), binder(INT)],
            order("$0", "$1", Order::Less),
        ),
        guarded(
            vec![binder(INT), binder(INT)],
            order("$0", "$1", Order::Equal),
        ),
        guarded(
            vec![binder(INT), binder(INT)],
            order("$0", "$1", Order::Greater),
        ),
    ];
    assert!(gaps(&signature, &rows, &[INT, INT]).is_empty());
    assert_eq!(gaps(&signature, &rows[..2], &[INT, INT]).len(), 1);
}

#[test]
fn points_realize_every_interval_and_avoid_excluded_values() {
    let constants = [0, 10]
        .map(BigInt::from)
        .into_iter()
        .collect::<BTreeSet<_>>();
    let none = BTreeSet::new();
    assert_eq!(
        points(&constants, &none),
        [0, 1, 10, 11, -1].map(BigInt::from)
    );
    let excluded = (1..10).map(BigInt::from).collect::<BTreeSet<_>>();
    assert_eq!(
        points(&constants, &excluded),
        [0, 10, 11, -1].map(BigInt::from)
    );
    let table = (0..8).map(BigInt::from).collect::<BTreeSet<_>>();
    assert_eq!(points(&BTreeSet::new(), &table), [BigInt::from(8)]);
}

// ---------------------------------------------------------------------------
// The guard decider against brute force

/// A small deterministic generator (xorshift64*).
struct Random(u64);

impl Random {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, bound: u64) -> usize {
        usize::try_from(self.next() % bound).unwrap()
    }

    fn small(&mut self) -> i64 {
        i64::try_from(self.below(9)).unwrap() - 4
    }
}

const SUBJECTS: [&str; 2] = ["$0", "$1"];
const PROPS: [&str; 2] = ["p", "q"];
/// Every constant lies in [-4, 4], so every region of the integers that a
/// guard can distinguish has a representative in this range.
const RANGE: std::ops::RangeInclusive<i64> = -9..=9;

fn random_atom(random: &mut Random, orders: bool) -> Formula {
    let subject = SUBJECTS[random.below(2)];
    match random.below(if orders { 5 } else { 4 }) {
        0 => bound(subject, Bound::Below, random.small()),
        1 => bound(subject, Bound::At, random.small()),
        2 => bound(subject, Bound::Above, random.small()),
        3 => opaque(PROPS[random.below(2)]),
        _ => order(
            "$0",
            "$1",
            [Order::Less, Order::Equal, Order::Greater][random.below(3)],
        ),
    }
}

fn random_formula(random: &mut Random, depth: u32, orders: bool) -> Formula {
    if depth == 0 || random.below(3) == 0 {
        return random_atom(random, orders);
    }
    match random.below(3) {
        0 => random_formula(random, depth - 1, orders).not(),
        1 => and(
            random_formula(random, depth - 1, orders),
            random_formula(random, depth - 1, orders),
        ),
        _ => or(
            random_formula(random, depth - 1, orders),
            random_formula(random, depth - 1, orders),
        ),
    }
}

/// The value of a formula at concrete subjects and propositions.
fn truth(formula: &Formula, values: [i64; 2], props: [bool; 2]) -> bool {
    let value = |subject: &str| values[SUBJECTS.iter().position(|name| *name == subject).unwrap()];
    match formula {
        Formula::Atom(Atom::Opaque(key)) => {
            props[PROPS.iter().position(|name| name == key).unwrap()]
        }
        Formula::Atom(Atom::Bound {
            subject,
            bound,
            constant,
        }) => {
            let value = BigInt::from(value(subject));
            match bound {
                Bound::Below => value < *constant,
                Bound::At => value == *constant,
                Bound::Above => *constant < value,
            }
        }
        Formula::Atom(Atom::Order { left, right, order }) => {
            let ordering = value(left).cmp(&value(right));
            matches!(
                (order, ordering),
                (Order::Less, std::cmp::Ordering::Less)
                    | (Order::Equal, std::cmp::Ordering::Equal)
                    | (Order::Greater, std::cmp::Ordering::Greater)
            )
        }
        Formula::Not(inner) => !truth(inner, values, props),
        Formula::And(left, right) => truth(left, values, props) && truth(right, values, props),
        Formula::Or(left, right) => truth(left, values, props) || truth(right, values, props),
        Formula::Constant(value) => *value,
    }
}

fn admitted(value: i64, fact: Option<&Fact>) -> bool {
    match fact {
        Some(Fact::Equal(fixed)) => BigInt::from(value) == *fixed,
        Some(Fact::Excluded(excluded)) => !excluded.contains(&BigInt::from(value)),
        Some(Fact::Within(intervals)) => intervals.iter().any(|(low, high)| {
            low.as_ref().is_none_or(|low| *low <= BigInt::from(value))
                && high
                    .as_ref()
                    .is_none_or(|high| BigInt::from(value) <= *high)
        }),
        None => true,
    }
}

/// A valuation in range, consistent with the facts, under which no guard holds.
fn brute_counterexample(
    guards: &[&Formula],
    facts: &BTreeMap<String, Fact>,
) -> Option<([i64; 2], [bool; 2])> {
    for first in RANGE {
        if !admitted(first, facts.get("$0")) {
            continue;
        }
        for second in RANGE {
            if !admitted(second, facts.get("$1")) {
                continue;
            }
            for mask in 0..4_u8 {
                let props = [mask & 1 == 1, mask & 2 == 2];
                if !guards
                    .iter()
                    .any(|guard| truth(guard, [first, second], props))
                {
                    return Some(([first, second], props));
                }
            }
        }
    }
    None
}

fn random_facts(random: &mut Random) -> BTreeMap<String, Fact> {
    let mut facts = BTreeMap::new();
    match random.below(3) {
        0 => {}
        1 => {
            facts.insert("$0".to_owned(), Fact::Equal(BigInt::from(random.small())));
        }
        _ => {
            let excluded = (0..random.below(4))
                .map(|_| BigInt::from(random.small()))
                .collect();
            facts.insert("$0".to_owned(), Fact::Excluded(excluded));
        }
    }
    facts
}

/// Whether a counterexample is a real valuation that falsifies every guard.
/// A subject no bound mentions takes no value; any value then does.
fn genuine(
    counterexample: &Counterexample,
    guards: &[&Formula],
    facts: &BTreeMap<String, Fact>,
) -> bool {
    RANGE.clone().any(|first| {
        RANGE.clone().any(|second| {
            let values = [first, second];
            let fixed = SUBJECTS.iter().zip(values).all(|(subject, value)| {
                admitted(value, facts.get(*subject))
                    && counterexample
                        .values
                        .get(*subject)
                        .is_none_or(|chosen| *chosen == BigInt::from(value))
            });
            let props = PROPS.map(|key| counterexample.truths.get(key).copied().unwrap_or(false));
            fixed && !guards.iter().any(|guard| truth(guard, values, props))
        })
    })
}

#[test]
fn the_decider_is_exact_on_bounds_and_propositions() {
    let mut random = Random(0x9E37_79B9_7F4A_7C15);
    let mut verdicts = [0_usize; 2];
    for _ in 0..4000 {
        let count = 1 + random.below(4);
        let formulas = (0..count)
            .map(|_| random_formula(&mut random, 3, false))
            .collect::<Vec<_>>();
        let guards = formulas.iter().collect::<Vec<_>>();
        let facts = random_facts(&mut random);
        let brute = brute_counterexample(&guards, &facts);
        match decide(&guards, &facts, &Projections::new()) {
            Verdict::Valid => {
                verdicts[0] += 1;
                assert!(
                    brute.is_none(),
                    "decided valid, but {brute:?} refutes {guards:?} under {facts:?}"
                );
            }
            Verdict::Refuted(counterexample) => {
                verdicts[1] += 1;
                assert!(
                    brute.is_some(),
                    "refuted {guards:?} under {facts:?}, but no valuation in range does"
                );
                assert!(
                    genuine(&counterexample, &guards, &facts),
                    "{counterexample:?} does not refute {guards:?} under {facts:?}"
                );
            }
            Verdict::Undecided => panic!("small guards are always decided"),
        }
    }
    assert!(verdicts.iter().all(|count| *count > 100), "{verdicts:?}");
}

#[test]
fn the_decider_never_calls_an_invalid_disjunction_valid() {
    let mut random = Random(0xD1B5_4A32_D192_ED03);
    let mut valid = 0;
    for _ in 0..4000 {
        let count = 1 + random.below(4);
        let formulas = (0..count)
            .map(|_| random_formula(&mut random, 3, true))
            .collect::<Vec<_>>();
        let guards = formulas.iter().collect::<Vec<_>>();
        let facts = random_facts(&mut random);
        if let Verdict::Valid = decide(&guards, &facts, &Projections::new()) {
            valid += 1;
            assert!(
                brute_counterexample(&guards, &facts).is_none(),
                "decided valid, but brute force refutes {guards:?} under {facts:?}"
            );
        }
    }
    // The property is not vacuous.
    assert!(valid > 100, "only {valid} valid disjunctions generated");
}

// ---------------------------------------------------------------------------
// Bit facts between a subject and its projections

/// `$0`, `bitRangeInt($0, 0, 2)`, `bitRangeInt($0, 2, 2)` and `$0 &Int 5`.
const BIT_SUBJECTS: [&str; 4] = ["$0", "low", "high", "masked"];

fn bit_projections() -> Projections {
    let range = |offset: i64, length: i64| Projection::BitRange {
        offset: BigInt::from(offset),
        length: BigInt::from(length),
    };
    [
        ("low", range(0, 2)),
        ("high", range(2, 2)),
        ("masked", Projection::Mask(BigInt::from(5))),
    ]
    .into_iter()
    .map(|(subject, projection)| (subject.to_owned(), ("$0".to_owned(), projection)))
    .collect()
}

/// The value of each bit subject at `x`.
fn bit_values(x: i64) -> [i64; 4] {
    [x, x.rem_euclid(4), (x >> 2).rem_euclid(4), x & 5]
}

fn bit_truth(formula: &Formula, x: i64) -> bool {
    let values = bit_values(x);
    match formula {
        Formula::Atom(Atom::Bound {
            subject,
            bound,
            constant,
        }) => {
            let index = BIT_SUBJECTS
                .iter()
                .position(|name| name == subject)
                .unwrap();
            let value = BigInt::from(values[index]);
            match bound {
                Bound::Below => value < *constant,
                Bound::At => value == *constant,
                Bound::Above => *constant < value,
            }
        }
        Formula::Not(inner) => !bit_truth(inner, x),
        Formula::And(left, right) => bit_truth(left, x) && bit_truth(right, x),
        Formula::Or(left, right) => bit_truth(left, x) || bit_truth(right, x),
        Formula::Constant(value) => *value,
        Formula::Atom(_) => unreachable!("bit formulas have bounds only"),
    }
}

fn random_bit_formula(random: &mut Random, depth: u32) -> Formula {
    if depth == 0 || random.below(3) == 0 {
        let subject = BIT_SUBJECTS[random.below(4)];
        let constant = if subject == "$0" {
            i64::try_from(random.below(24)).unwrap() - 4
        } else {
            i64::try_from(random.below(8)).unwrap() - 1
        };
        let bound = [Bound::Below, Bound::At, Bound::At, Bound::Above][random.below(4)];
        return super::Formula::Atom(Atom::Bound {
            subject: subject.to_owned(),
            bound,
            constant: BigInt::from(constant),
        });
    }
    match random.below(3) {
        0 => random_bit_formula(random, depth - 1).not(),
        1 => and(
            random_bit_formula(random, depth - 1),
            random_bit_formula(random, depth - 1),
        ),
        _ => or(
            random_bit_formula(random, depth - 1),
            random_bit_formula(random, depth - 1),
        ),
    }
}

#[test]
fn bit_facts_never_make_an_invalid_disjunction_valid() {
    let projections = bit_projections();
    let mut random = Random(0x0BAD_5EED_1234_5678);
    let mut valid = 0;
    for _ in 0..6000 {
        let count = 1 + random.below(5);
        let formulas = (0..count)
            .map(|_| random_bit_formula(&mut random, 3))
            .collect::<Vec<_>>();
        let guards = formulas.iter().collect::<Vec<_>>();
        let facts = BTreeMap::new();
        if let Verdict::Valid = decide(&guards, &facts, &projections) {
            valid += 1;
            // Every constant lies in [-4, 20), so [-64, 64) has a
            // representative of every region the guards distinguish.
            let gap = (-64..64).find(|x| !guards.iter().any(|guard| bit_truth(guard, *x)));
            assert!(
                gap.is_none(),
                "decided valid, but {gap:?} falsifies every guard of {guards:?}"
            );
        }
    }
    assert!(valid > 100, "only {valid} valid disjunctions generated");
}

#[test]
fn templates_cover_their_cubes_and_nothing_outside_their_range() {
    let projections = bit_projections();
    let in_range = || and(bound("$0", Bound::Above, -1), bound("$0", Bound::Below, 16));
    // `k::bits!("hh __")` for each of the four values of the high run.
    let rows = (0..4)
        .map(|value| and(in_range(), bound("high", Bound::At, value)))
        .collect::<Vec<_>>();
    let guards = rows.iter().collect::<Vec<_>>();
    match decide(&guards, &BTreeMap::new(), &projections) {
        Verdict::Refuted(counterexample) => {
            let x = counterexample.values["$0"].clone();
            assert!(x == BigInt::from(16) || x < BigInt::from(0), "{x}");
        }
        verdict => panic!("{verdict:?}"),
    }
    let outside = [bound("$0", Bound::Below, 0), bound("$0", Bound::Above, 15)];
    let guards = rows.iter().chain(&outside).collect::<Vec<_>>();
    assert!(matches!(
        decide(&guards, &BTreeMap::new(), &projections),
        Verdict::Valid
    ));
    // Without the facts, `high` is an independent unknown and may be 4.
    assert!(matches!(
        decide(&guards, &BTreeMap::new(), &Projections::new()),
        Verdict::Refuted(_)
    ));
    // Three of the four cubes leave `high == 3` uncovered.
    let guards = rows[..3].iter().chain(&outside).collect::<Vec<_>>();
    assert!(matches!(
        decide(&guards, &BTreeMap::new(), &projections),
        Verdict::Refuted(_)
    ));
}

#[test]
fn orders_no_integers_realize_together_are_skipped() {
    // No integers make `a == b`, `b == c` and `a != c` hold, nor `a == b`,
    // `a < 0` and `0 < b`: read together, the orders and bounds make each
    // conjunction's negation valid.
    let equal = |left: &str, right: &str| order(left, right, Order::Equal);
    let chain = and(
        equal("$0", "$1"),
        and(equal("$1", "$2"), equal("$0", "$2").not()),
    );
    let verdict = decide(&[&chain.not()], &BTreeMap::new(), &Projections::new());
    assert!(matches!(verdict, Verdict::Valid), "{verdict:?}");
    let bounded = and(
        equal("$0", "$1"),
        and(bound("$0", Bound::Below, 0), bound("$1", Bound::Above, 0)),
    );
    let verdict = decide(&[&bounded.not()], &BTreeMap::new(), &Projections::new());
    assert!(matches!(verdict, Verdict::Valid), "{verdict:?}");
}

#[test]
fn a_size_is_never_negative() {
    // `pc < 0` and `size <= pc` cannot both hold when `size` is a size.
    let size = "list:Size($1)";
    let both = and(
        bound("$0", Bound::Below, 0),
        order("$0", size, Order::Less).not(),
    );
    let projections = Projections::from([(size.to_owned(), (size.to_owned(), Projection::Size))]);
    let verdict = decide(&[&both.clone().not()], &BTreeMap::new(), &projections);
    assert!(matches!(verdict, Verdict::Valid), "{verdict:?}");
    let verdict = decide(&[&both.not()], &BTreeMap::new(), &Projections::new());
    assert!(matches!(verdict, Verdict::Refuted(_)), "{verdict:?}");
}

// ---------------------------------------------------------------------------
// Complements, `k::matches!` expansion, minimized refutations, ranges

/// `KItem`, which every sort injects into.
fn kitem() -> Sort {
    Sort::Declared(
        StableItemId::new(
            PackageId::new("KRS-FRAMEWORK", "krs", "0.1.0", "test").unwrap(),
            ["framework"],
            "KItem",
            ItemKind::Sort,
            "",
        )
        .unwrap(),
    )
}

/// `Kind = A | B`, `Shape = Circle(Int) | Pair(Kind, Kind)`, and `Exp`
/// holding `Shape`s, `Int`s and `Neg(Int)`, below `KItem` with `Kind`.
struct Shapes {
    signature: Signature,
    a: StableItemId,
    b: StableItemId,
    circle: StableItemId,
    pair: StableItemId,
    neg: StableItemId,
    kind: Sort,
    shape: Sort,
    exp: Sort,
}

fn shapes() -> Shapes {
    let (a, b) = (variant("Kinds", "A"), variant("Kinds", "B"));
    let (circle, pair) = (variant("Shapes", "Circle"), variant("Shapes", "Pair"));
    let neg = variant("Exps", "Neg");
    let (kind, shape, exp) = (sort("Kind"), sort("Shape"), sort("Exp"));
    let signature = Builder::new()
        .constructor(&a, kind.clone(), &[])
        .constructor(&b, kind.clone(), &[])
        .constructor(&circle, shape.clone(), &[INT])
        .constructor(&pair, shape.clone(), &[kind.clone(), kind.clone()])
        .constructor(&neg, exp.clone(), &[INT])
        .subsort(shape.clone(), exp.clone())
        .subsort(INT, exp.clone())
        .subsort(exp.clone(), kitem())
        .subsort(kind.clone(), kitem())
        .build();
    Shapes {
        signature,
        a,
        b,
        circle,
        pair,
        neg,
        kind,
        shape,
        exp,
    }
}

/// A value, as the lint's heads see it.
#[derive(Clone, Debug)]
enum Value {
    Constructor(StableItemId, Vec<Value>),
    Int(i64),
    Bool(bool),
    /// A value of a family other than Int and Bool.
    Other(Sort),
}

impl Value {
    fn head(&self) -> Head {
        match self {
            Self::Constructor(id, _) => Head::Constructor {
                id: id.clone(),
                instance: Vec::new(),
            },
            Self::Int(_) => Head::Family(INT),
            Self::Bool(_) => Head::Family(BOOL),
            Self::Other(sort) => Head::Family(sort.clone()),
        }
    }
}

/// Values of every head of `sort`, constructors over values of their
/// argument sorts.
fn values(signature: &Signature, sort: &Sort) -> Vec<Value> {
    let mut all = Vec::new();
    for head in signature.heads(sort) {
        match head {
            Head::Constructor { id, instance } => {
                let mut combined = vec![Vec::new()];
                for argument in signature.arguments(&id, &instance) {
                    let choices = values(signature, &argument);
                    combined = combined
                        .into_iter()
                        .flat_map(|prefix: Vec<Value>| {
                            choices.iter().map(move |choice| {
                                let mut next = prefix.clone();
                                next.push(choice.clone());
                                next
                            })
                        })
                        .collect();
                }
                all.extend(
                    combined
                        .into_iter()
                        .map(|arguments| Value::Constructor(id.clone(), arguments)),
                );
            }
            Head::Family(family) if family == INT => {
                all.extend([-1, 0, 3].map(Value::Int));
            }
            Head::Family(family) if family == BOOL => {
                all.extend([true, false].map(Value::Bool));
            }
            Head::Family(family) => all.push(Value::Other(family)),
        }
    }
    all
}

/// Whether a pattern matches a value, recording the Ints it binds by path.
fn matched(
    signature: &Signature,
    pattern: &Pattern,
    value: &Value,
    path: &mut Vec<usize>,
    ints: &mut BTreeMap<String, i64>,
) -> bool {
    if let Value::Int(number) = value {
        ints.insert(super::path_text(path), *number);
    }
    match (pattern, value) {
        (Pattern::Binder(sort), _) => signature.binder_covers(sort, &value.head()),
        (Pattern::Family(family), _) => value.head() == Head::Family(family.clone()),
        (Pattern::Literal { sort, value: text }, Value::Int(number)) => {
            *sort == INT && *text == number.to_string()
        }
        (Pattern::Literal { sort, value: text }, Value::Bool(truth)) => {
            *sort == BOOL && *text == truth.to_string()
        }
        (Pattern::Constructor { id, arguments, .. }, Value::Constructor(other, values)) => {
            id == other
                && arguments
                    .iter()
                    .zip(values)
                    .enumerate()
                    .all(|(index, (pattern, value))| {
                        path.push(index);
                        let matched = matched(signature, pattern, value, path, ints);
                        path.pop();
                        matched
                    })
        }
        _ => false,
    }
}

/// The truth of a residual condition over the Ints a match bound.
fn residual_holds(formula: &Formula, ints: &BTreeMap<String, i64>) -> bool {
    match formula {
        Formula::Atom(Atom::Bound {
            subject,
            bound: Bound::At,
            constant,
        }) => BigInt::from(ints[subject]) == *constant,
        Formula::Not(inner) => !residual_holds(inner, ints),
        Formula::And(left, right) => residual_holds(left, ints) && residual_holds(right, ints),
        Formula::Constant(value) => *value,
        other => panic!("unexpected residual {other:?}"),
    }
}

/// Whether some refined pattern matches a value and its residual holds.
fn refined_matches(signature: &Signature, refined: &[super::Refined], value: &Value) -> bool {
    refined.iter().any(|(pattern, residual)| {
        let mut ints = BTreeMap::new();
        matched(signature, pattern, value, &mut vec![0], &mut ints)
            && residual
                .iter()
                .all(|formula| residual_holds(formula, &ints))
    })
}

/// Patterns over [`shapes`], each with the sort its complement is taken in.
fn shape_patterns(shapes: &Shapes) -> Vec<(Pattern, Sort)> {
    let a = || construct(&shapes.a, vec![]);
    vec![
        (binder(shapes.exp.clone()), kitem()),
        (binder(shapes.shape.clone()), shapes.exp.clone()),
        (binder(INT), kitem()),
        (
            construct(&shapes.circle, vec![binder(INT)]),
            shapes.shape.clone(),
        ),
        (
            construct(&shapes.circle, vec![int(3)]),
            shapes.shape.clone(),
        ),
        (construct(&shapes.circle, vec![int(3)]), kitem()),
        (
            construct(&shapes.pair, vec![a(), binder(shapes.kind.clone())]),
            shapes.shape.clone(),
        ),
        (
            construct(&shapes.pair, vec![a(), construct(&shapes.b, vec![])]),
            kitem(),
        ),
        (construct(&shapes.neg, vec![int(0)]), shapes.exp.clone()),
        (int(0), INT),
        (int(0), shapes.exp.clone()),
        (boolean(true), BOOL),
        (Pattern::Family(INT), shapes.exp.clone()),
        (Pattern::Family(kitem()), kitem()),
    ]
}

#[test]
fn a_complement_matches_exactly_what_its_pattern_does_not() {
    let shapes = shapes();
    let signature = &shapes.signature;
    for (pattern, sort) in shape_patterns(&shapes) {
        let complement = super::complement(signature, &pattern, &sort, &[0]).unwrap();
        let values = values(signature, &sort);
        assert!(values.len() > 1, "{sort:?}");
        for value in values {
            let direct = matched(
                signature,
                &pattern,
                &value,
                &mut vec![0],
                &mut BTreeMap::new(),
            );
            let complemented = refined_matches(signature, &complement, &value);
            assert_ne!(
                direct, complemented,
                "{value:?}: {pattern:?} and its complement {complement:?} in {sort:?}"
            );
        }
    }
    // A union's complement is the intersection of the complements.
    let union = [
        construct(&shapes.circle, vec![binder(INT)]),
        construct(
            &shapes.pair,
            vec![construct(&shapes.a, vec![]), binder(shapes.kind.clone())],
        ),
    ];
    let complement = super::complement_all(signature, &union, &shapes.exp, &[0]).unwrap();
    for value in values(signature, &shapes.exp) {
        let direct = union.iter().any(|pattern| {
            matched(
                signature,
                pattern,
                &value,
                &mut vec![0],
                &mut BTreeMap::new(),
            )
        });
        assert_ne!(
            direct,
            refined_matches(signature, &complement, &value),
            "{value:?}"
        );
    }
    // A binder of a family's sort would also match its subsorts' constructors.
    let open = super::complement(
        signature,
        &construct(&shapes.neg, vec![binder(INT)]),
        &kitem(),
        &[0],
    )
    .unwrap();
    assert!(
        open.iter()
            .any(|(pattern, _)| matches!(pattern, Pattern::Family(sort) if *sort == kitem()))
    );
    assert!(
        !open
            .iter()
            .any(|(pattern, _)| matches!(pattern, Pattern::Binder(sort) if *sort == kitem()))
    );
}

#[test]
fn a_meet_matches_exactly_what_both_patterns_match() {
    let shapes = shapes();
    let signature = &shapes.signature;
    let patterns = shape_patterns(&shapes);
    for (left, _) in &patterns {
        for (right, _) in &patterns {
            let met = super::meet(signature, left, right).unwrap();
            for value in values(signature, &kitem()) {
                let both = matched(signature, left, &value, &mut vec![0], &mut BTreeMap::new())
                    && matched(signature, right, &value, &mut vec![0], &mut BTreeMap::new());
                let any = met.iter().any(|pattern| {
                    matched(
                        signature,
                        pattern,
                        &value,
                        &mut vec![0],
                        &mut BTreeMap::new(),
                    )
                });
                assert_eq!(both, any, "{value:?} in {left:?} and {right:?}: {met:?}");
            }
        }
    }
    assert!(super::meet(signature, &Pattern::Opaque, &binder(INT)).is_none());
}

/// `k::matches!(Circle(_), shape)` on argument 0, as the atom `m`.
fn circle_test(shapes: &Shapes) -> BTreeMap<String, super::Test> {
    BTreeMap::from([(
        "m".to_owned(),
        super::Test {
            subject: super::TestSubject::Binder(vec![0]),
            sort: shapes.shape.clone(),
            alternatives: vec![construct(&shapes.circle, vec![binder(INT)])],
        },
    )])
}

/// A pattern rendered with its head names.
fn show(pattern: &Pattern) -> String {
    match pattern {
        Pattern::Binder(sort) => format!("_:{}", super::sort_name(sort)),
        Pattern::Constructor { id, arguments, .. } => format!(
            "{}({})",
            super::display_name(id),
            arguments.iter().map(show).collect::<Vec<_>>().join(", ")
        ),
        Pattern::Literal { value, .. } => value.clone(),
        Pattern::Family(sort) => format!("family {}", super::sort_name(sort)),
        Pattern::Opaque => "opaque".to_owned(),
    }
}

#[test]
fn a_matches_test_expands_into_one_row_per_truth_assignment() {
    let shapes = shapes();
    // `notBool (k::matches!(Circle(_), shape) && flag > 5)`.
    let guard = and(opaque("m"), bound("$1", Bound::Above, 5)).not();
    let rows = super::expand(
        &shapes.signature,
        &[binder(shapes.shape.clone()), binder(INT)],
        &guard,
        &circle_test(&shapes),
        &BTreeMap::new(),
    )
    .unwrap();
    let shown = rows
        .iter()
        .map(|(patterns, guard)| {
            format!(
                "{} if {guard:?}",
                patterns.iter().map(show).collect::<Vec<_>>().join(", ")
            )
        })
        .collect::<Vec<_>>();
    expect_test::expect![[r#"
        [
            "Shapes::Pair(_:Kind, _:Kind), _:Int if Constant(true)",
            "Shapes::Circle(_:Int), _:Int if Not(Atom(Bound { subject: \"$1\", bound: Above, constant: 5 }))",
        ]
    "#]]
    .assert_debug_eq(&shown);
}

#[test]
fn a_nested_catch_all_over_a_parameter_covers_the_other_shapes() {
    let shapes = shapes();
    let signature = &shapes.signature;
    let flag = || bound("$1", Bound::Above, 0);
    // `Area`: `if flag > 0 { match shape { Circle { r } => .., _ => 0 } } else { 1 }`.
    let catch_all = and(flag(), opaque("m").not());
    let mut rows = vec![
        guarded(
            vec![construct(&shapes.circle, vec![binder(INT)]), binder(INT)],
            flag(),
        ),
        guarded(
            vec![binder(shapes.shape.clone()), binder(INT)],
            flag().not(),
        ),
    ];
    // Read as an opaque atom, the catch-all leaves `Pair` uncovered.
    let mut opaque_rows = rows.clone();
    opaque_rows.push(guarded(
        vec![binder(shapes.shape.clone()), binder(INT)],
        catch_all.clone(),
    ));
    assert_eq!(
        gaps(signature, &opaque_rows, &[shapes.shape.clone(), INT]),
        ["(Shapes::Pair(_, _), 1)"]
    );
    let expanded = super::expand(
        signature,
        &[binder(shapes.shape.clone()), binder(INT)],
        &catch_all,
        &circle_test(&shapes),
        &BTreeMap::new(),
    )
    .unwrap();
    rows.extend(
        expanded
            .into_iter()
            .map(|(patterns, guard)| guarded(patterns, guard)),
    );
    assert!(gaps(signature, &rows, &[shapes.shape, INT]).is_empty());
}

/// Every valuation in range that the counterexample's kept values,
/// orders and truths describe falsifies every guard.
fn refutes_everywhere(
    counterexample: &Counterexample,
    guards: &[&Formula],
    facts: &BTreeMap<String, Fact>,
) -> bool {
    RANGE.clone().all(|first| {
        RANGE.clone().all(|second| {
            (0..4_u8).all(|mask| {
                let values = [first, second];
                let props = [mask & 1 == 1, mask & 2 == 2];
                let described = SUBJECTS.iter().zip(values).all(|(subject, value)| {
                    admitted(value, facts.get(*subject))
                        && counterexample
                            .values
                            .get(*subject)
                            .is_none_or(|chosen| *chosen == BigInt::from(value))
                }) && PROPS.iter().zip(props).all(|(key, truth)| {
                    counterexample
                        .truths
                        .get(*key)
                        .is_none_or(|chosen| *chosen == truth)
                }) && counterexample.orders.iter().all(
                    |((left, right), chosen)| truth(&order(left, right, *chosen), values, props),
                );
                !described || !guards.iter().any(|guard| truth(guard, values, props))
            })
        })
    })
}

#[test]
fn a_reported_condition_is_always_a_refutation() {
    let mut random = Random(0x2545_F491_4F6C_DD1D);
    let mut refuted = 0;
    for _ in 0..4000 {
        let count = 1 + random.below(4);
        let formulas = (0..count)
            .map(|_| random_formula(&mut random, 3, true))
            .collect::<Vec<_>>();
        let guards = formulas.iter().collect::<Vec<_>>();
        let facts = random_facts(&mut random);
        if let Verdict::Refuted(counterexample) = decide(&guards, &facts, &Projections::new()) {
            refuted += 1;
            assert!(
                refutes_everywhere(&counterexample, &guards, &facts),
                "{counterexample:?} describes a valuation some guard of {guards:?} holds on under {facts:?}"
            );
        }
    }
    assert!(refuted > 100, "only {refuted} refutations generated");
}

#[test]
fn atoms_that_only_matter_together_stay_in_the_condition() {
    // `SignedLess`: each guard needs both signs.
    let sign = |subject: &str, value: i64| bound(subject, Bound::At, value);
    let formulas = [(1, 1), (1, -1), (-1, 1), (-1, -1)]
        .map(|(left, right)| and(sign("$0", left), sign("$1", right)));
    let guards = formulas.iter().collect::<Vec<_>>();
    let Verdict::Refuted(counterexample) = decide(&guards, &BTreeMap::new(), &Projections::new())
    else {
        panic!("a sign may be 0");
    };
    // Dropping every atom that alone changes nothing would claim that no
    // argument is covered at all.
    assert!(!counterexample.values.is_empty(), "{counterexample:?}");
    assert!(refutes_everywhere(
        &counterexample,
        &guards,
        &BTreeMap::new()
    ));
    assert_eq!(counterexample.values.len(), 1, "{counterexample:?}");
}

#[test]
fn a_range_limits_the_values_the_decider_enumerates() {
    let guards = [bound("$0", Bound::At, 1), bound("$0", Bound::At, -1)];
    let guards = guards.iter().collect::<Vec<_>>();
    let range = |intervals: &[(i64, i64)]| {
        BTreeMap::from([(
            "$0".to_owned(),
            Fact::Within(
                intervals
                    .iter()
                    .map(|(low, high)| (Some(BigInt::from(*low)), Some(BigInt::from(*high))))
                    .collect(),
            ),
        )])
    };
    let two = range(&[(-1, -1), (1, 1)]);
    assert!(matches!(
        decide(&guards, &two, &Projections::new()),
        Verdict::Valid
    ));
    let Verdict::Refuted(counterexample) = decide(&guards, &range(&[(-1, 1)]), &Projections::new())
    else {
        panic!("0 is in the range");
    };
    assert_eq!(counterexample.values.get("$0"), Some(&BigInt::from(0)));
    // Unbounded on one side.
    let above = BTreeMap::from([(
        "$0".to_owned(),
        Fact::Within(vec![(Some(BigInt::from(1)), None)]),
    )]);
    let Verdict::Refuted(counterexample) = decide(&guards, &above, &Projections::new()) else {
        panic!("2 is in the range");
    };
    assert_eq!(counterexample.values.get("$0"), Some(&BigInt::from(2)));
}

#[test]
fn ranges_merge_and_keep_their_kind() {
    let interval = |low: i64, high: Option<i64>| (Some(BigInt::from(low)), high.map(BigInt::from));
    let merged = super::merged(vec![
        interval(5, Some(6)),
        interval(0, Some(1)),
        interval(2, Some(3)),
        interval(10, None),
        interval(12, Some(20)),
    ]);
    assert_eq!(
        merged,
        [
            interval(0, Some(3)),
            interval(5, Some(6)),
            interval(10, None)
        ]
    );
    let ints = super::Range::Ints(vec![interval(0, Some(0))]);
    let bools = super::Range::Bools(BTreeSet::from([true]));
    assert!(ints.clone().union(bools.clone()).is_none());
    assert_eq!(
        bools.union(super::Range::Bools(BTreeSet::from([false]))),
        Some(super::Range::Bools(BTreeSet::from([false, true])))
    );
    assert_eq!(
        ints.union(super::Range::Ints(vec![interval(1, Some(1))])),
        Some(super::Range::Ints(vec![interval(0, Some(1))]))
    );
}

// ---------------------------------------------------------------------------
// Reading guards with partial operations

mod reading {
    use std::collections::BTreeMap;

    use krs_ir::{ApplicationRef, BuiltinOperation, NodeOrigin, SemanticId, SourceMapKey};
    use krs_ir_levels::{SemanticSortRef as Sort, SemanticTerm};

    use super::super::{Formula, GuardReader, Projections, Signature, Verdict, decide};
    use super::{BOOL, INT};

    use BuiltinOperation::{
        BoolAndThen, BoolNot, BoolOrElse, IntGreater, IntLess, IntLessEqual, IntShiftLeft, IntSub,
        IntTDiv,
    };

    fn origin() -> NodeOrigin {
        NodeOrigin::new(
            SourceMapKey::new("sem.coverage-reading").unwrap(),
            krs_ir::testing::authored(0, 1),
        )
    }

    fn variable(name: &str) -> SemanticTerm {
        SemanticTerm::variable(origin(), INT, SemanticId::new(name.to_owned()).unwrap())
    }

    fn int(value: i64) -> SemanticTerm {
        SemanticTerm::token(origin(), INT, value.to_string()).unwrap()
    }

    fn apply(operation: BuiltinOperation, arguments: Vec<SemanticTerm>) -> SemanticTerm {
        let sort = Sort::Builtin(operation.result_sort().builtin().unwrap());
        SemanticTerm::application(
            origin(),
            sort,
            ApplicationRef::Builtin(operation),
            arguments,
        )
    }

    /// Reads a guard over `x` (argument 0) and `w` (argument 1).
    fn read(term: &SemanticTerm) -> Option<Formula> {
        let signature = Signature::default();
        let paths = BTreeMap::from([
            (SemanticId::new("x".to_owned()).unwrap(), vec![0]),
            (SemanticId::new("w".to_owned()).unwrap(), vec![1]),
        ]);
        let mut reader = GuardReader::new(&signature, &paths, None);
        reader.guard(term)
    }

    /// `1 << (w - 1)`, defined where `w >= 1`.
    fn half_range() -> SemanticTerm {
        apply(
            IntShiftLeft,
            vec![int(1), apply(IntSub, vec![variable("w"), int(1)])],
        )
    }

    #[test]
    fn a_shift_defined_where_an_earlier_conjunct_holds_counts() {
        let positive = || apply(IntGreater, vec![variable("w"), int(0)]);
        let low = apply(
            BoolAndThen,
            vec![
                positive(),
                apply(IntLess, vec![variable("x"), half_range()]),
            ],
        );
        let high = apply(
            BoolAndThen,
            vec![
                positive(),
                apply(
                    BoolNot,
                    vec![apply(IntLess, vec![variable("x"), half_range()])],
                ),
            ],
        );
        let none = apply(IntLessEqual, vec![variable("w"), int(0)]);
        let guards = [
            read(&none).unwrap(),
            read(&low).unwrap(),
            read(&high).unwrap(),
        ];
        let verdict = decide(
            &guards.iter().collect::<Vec<_>>(),
            &BTreeMap::new(),
            &Projections::new(),
        );
        assert!(matches!(verdict, Verdict::Valid), "{verdict:?}");
    }

    #[test]
    fn a_division_holds_only_where_its_divisor_is_not_zero() {
        let quotient = || apply(IntTDiv, vec![variable("x"), variable("w")]);
        let negative = apply(IntLess, vec![quotient(), int(0)]);
        let nonnegative = apply(BoolNot, vec![apply(IntLess, vec![quotient(), int(0)])]);
        let guards = [read(&negative).unwrap(), read(&nonnegative).unwrap()];
        let Verdict::Refuted(counterexample) = decide(
            &guards.iter().collect::<Vec<_>>(),
            &BTreeMap::new(),
            &Projections::new(),
        ) else {
            panic!("a zero divisor leaves both guards undefined");
        };
        assert_eq!(
            counterexample
                .values
                .get("$1")
                .map(ToString::to_string)
                .as_deref(),
            Some("0")
        );
    }

    #[test]
    fn a_lazy_connective_is_read_only_where_both_readings_agree() {
        let positive = || apply(IntGreater, vec![variable("w"), int(0)]);
        let quotient = || {
            apply(
                IntGreater,
                vec![apply(IntTDiv, vec![int(1), variable("w")]), int(0)],
            )
        };
        let and_then = || apply(BoolAndThen, vec![positive(), quotient()]);
        let or_else = || apply(BoolOrElse, vec![positive(), quotient()]);
        assert!(read(&and_then()).is_some());
        assert!(read(&apply(BoolNot, vec![and_then()])).is_none());
        assert!(read(&or_else()).is_none());
        assert!(read(&apply(BoolNot, vec![or_else()])).is_some());
        let compared = apply(
            BuiltinOperation::BoolEqual,
            vec![
                and_then(),
                SemanticTerm::token(origin(), BOOL, "false".to_owned()).unwrap(),
            ],
        );
        assert!(read(&compared).is_none());
    }

    fn declared(
        id: &krs_ir::StableItemId,
        sort: Sort,
        arguments: Vec<SemanticTerm>,
    ) -> SemanticTerm {
        SemanticTerm::application(
            origin(),
            sort,
            ApplicationRef::Declared(id.clone()),
            arguments,
        )
    }

    fn matches(subject: SemanticTerm, pattern: SemanticTerm) -> SemanticTerm {
        SemanticTerm::matches(origin(), BOOL, subject, pattern, Vec::new())
    }

    /// Reads a guard over `shape` (argument 0) with [`super::shapes`]'
    /// signature and `ranges`.
    fn read_shapes(
        shapes: &super::Shapes,
        term: &SemanticTerm,
        ranges: Option<&dyn super::super::RangeOf>,
    ) -> Option<(Formula, Vec<String>)> {
        let paths = BTreeMap::from([(SemanticId::new("shape".to_owned()).unwrap(), vec![0])]);
        let mut reader = GuardReader::new(&shapes.signature, &paths, ranges);
        let formula = reader.guard(term)?;
        let tests = reader
            .tests
            .values()
            .map(|test| format!("{:?} {}", test.subject, test.alternatives.len()))
            .collect();
        Some((formula, tests))
    }

    fn circle(shapes: &super::Shapes, argument: SemanticTerm) -> SemanticTerm {
        declared(&shapes.circle, shapes.shape.clone(), vec![argument])
    }

    fn wildcard(ordinal: usize) -> SemanticTerm {
        SemanticTerm::variable(origin(), INT, SemanticId::wildcard(ordinal))
    }

    #[test]
    fn a_linear_matches_test_is_read_as_pattern_matching() {
        let shapes = super::shapes();
        let shape = || {
            SemanticTerm::variable(
                origin(),
                shapes.shape.clone(),
                SemanticId::new("shape".to_owned()).unwrap(),
            )
        };
        let test = matches(shape(), circle(&shapes, wildcard(0)));
        let (formula, tests) = read_shapes(&shapes, &test, None).unwrap();
        assert!(
            matches!(formula, Formula::Atom(super::Atom::Opaque(_))),
            "{formula:?}"
        );
        assert_eq!(tests, ["Binder([0]) 1"]);
        // The same test negated is the same atom.
        let (negated, _) = read_shapes(&shapes, &apply(BoolNot, vec![test.clone()]), None).unwrap();
        assert_eq!(format!("{negated:?}"), format!("{:?}", formula.not()));
        // A pattern that repeats a local binder is an opaque atom only.
        let pair = |left: SemanticTerm, right: SemanticTerm| {
            declared(&shapes.pair, shapes.shape.clone(), vec![left, right])
        };
        let kind = |name: &str| {
            SemanticTerm::variable(
                origin(),
                shapes.kind.clone(),
                SemanticId::new(name.to_owned()).unwrap(),
            )
        };
        let (repeated, tests) =
            read_shapes(&shapes, &matches(shape(), pair(kind("k"), kind("k"))), None).unwrap();
        assert!(tests.is_empty());
        let (distinct, tests) =
            read_shapes(&shapes, &matches(shape(), pair(kind("k"), kind("l"))), None).unwrap();
        assert_eq!(tests, ["Binder([0]) 1"]);
        assert_ne!(format!("{repeated:?}"), format!("{distinct:?}"));
        // A binder the pattern does not bind leaves the guard unread.
        let unbound = SemanticTerm::variable(
            origin(),
            shapes.shape.clone(),
            SemanticId::new("other".to_owned()).unwrap(),
        );
        assert!(
            read_shapes(
                &shapes,
                &matches(unbound, circle(&shapes, wildcard(0))),
                None
            )
            .is_none()
        );
    }

    /// A function `Classify` of `Shape`s whose range is `Kinds::A`, and a
    /// function `Positive` whose range is `true`.
    struct Ranges {
        classify: krs_ir::StableItemId,
        positive: krs_ir::StableItemId,
        kind: Sort,
        a: krs_ir::StableItemId,
    }

    impl super::super::RangeOf for Ranges {
        fn range_of(&self, id: &krs_ir::StableItemId) -> Option<std::rc::Rc<super::super::Range>> {
            let range = if *id == self.classify {
                super::super::Range::Heads(std::collections::BTreeSet::from([
                    super::Head::Constructor {
                        id: self.a.clone(),
                        instance: Vec::new(),
                    },
                ]))
            } else if *id == self.positive {
                super::super::Range::Bools(std::collections::BTreeSet::from([true]))
            } else {
                return None;
            };
            Some(std::rc::Rc::new(range))
        }
    }

    #[test]
    fn ranges_restrict_virtual_columns_and_fix_bool_atoms() {
        let mut shapes = super::shapes();
        let (classify, positive) = (
            super::variant("Functions", "Classify"),
            super::variant("Functions", "Positive"),
        );
        shapes.signature.total_functions.insert(classify.clone());
        shapes.signature.total_functions.insert(positive.clone());
        let ranges = Ranges {
            classify: classify.clone(),
            positive: positive.clone(),
            kind: shapes.kind.clone(),
            a: shapes.a.clone(),
        };
        let shape = SemanticTerm::variable(
            origin(),
            shapes.shape.clone(),
            SemanticId::new("shape".to_owned()).unwrap(),
        );
        let classified = declared(&classify, ranges.kind.clone(), vec![shape.clone()]);
        let test = matches(
            classified,
            declared(&shapes.a, shapes.kind.clone(), Vec::new()),
        );
        let paths = BTreeMap::from([(SemanticId::new("shape".to_owned()).unwrap(), vec![0])]);
        let mut reader = GuardReader::new(&shapes.signature, &paths, Some(&ranges));
        reader.guard(&test).unwrap();
        let columns = reader.virtuals.values().collect::<Vec<_>>();
        assert_eq!(columns.len(), 1);
        assert_eq!(
            columns[0]
                .heads
                .as_ref()
                .map(std::collections::BTreeSet::len),
            Some(1)
        );
        let applied = declared(&positive, BOOL, vec![shape]);
        let (formula, _) = read_shapes(&shapes, &applied, Some(&ranges)).unwrap();
        assert!(matches!(formula, Formula::Constant(true)), "{formula:?}");
        let (formula, _) = read_shapes(&shapes, &applied, None).unwrap();
        assert!(matches!(formula, Formula::Atom(_)), "{formula:?}");
    }

    #[test]
    fn a_matches_test_on_a_ground_term_is_evaluated_as_matching() {
        use crate::equation_domain::{Evaluator, Ground, guard_holds};
        let shapes = super::shapes();
        let evaluator = Evaluator::new(&shapes.signature);
        let id = SemanticId::new("shape".to_owned()).unwrap();
        let shape = || SemanticTerm::variable(origin(), shapes.shape.clone(), id.clone());
        let circle_three = Ground::Term {
            id: shapes.circle.clone(),
            instance: Vec::new(),
            arguments: vec![Ground::Int(3)],
        };
        let environment = BTreeMap::from([(&id, circle_three)]);
        let holds = |pattern: SemanticTerm| {
            guard_holds(&evaluator, &matches(shape(), pattern), &environment)
        };
        let typed = |sort: Sort| {
            SemanticTerm::variable(origin(), sort, SemanticId::new("local".to_owned()).unwrap())
        };
        assert_eq!(holds(circle(&shapes, wildcard(0))), Some(true));
        assert_eq!(holds(circle(&shapes, int(3))), Some(true));
        assert_eq!(holds(circle(&shapes, int(4))), Some(false));
        let pair = declared(
            &shapes.pair,
            shapes.shape.clone(),
            vec![typed(shapes.kind.clone()), typed(shapes.kind.clone())],
        );
        assert_eq!(holds(pair), Some(false));
        // A local binder matches the values of its sort and its subsorts'.
        assert_eq!(holds(typed(shapes.exp.clone())), Some(true));
        assert_eq!(holds(typed(super::kitem())), Some(true));
        assert_eq!(holds(typed(shapes.kind.clone())), Some(false));
        assert_eq!(
            guard_holds(
                &evaluator,
                &apply(BoolNot, vec![matches(shape(), circle(&shapes, int(4)))]),
                &environment,
            ),
            Some(true)
        );
        // A subject the evaluation cannot compute decides nothing; an
        // undefined one makes the guard not hold.
        let unknown = super::variant("Functions", "Unknown");
        let applied = declared(&unknown, shapes.shape.clone(), Vec::new());
        assert_eq!(
            guard_holds(
                &evaluator,
                &matches(applied, circle(&shapes, wildcard(0))),
                &environment
            ),
            None
        );
        let undefined = circle(&shapes, apply(IntTDiv, vec![int(1), int(0)]));
        assert_eq!(
            guard_holds(
                &evaluator,
                &matches(undefined, circle(&shapes, wildcard(0))),
                &environment
            ),
            Some(false)
        );
    }

    #[test]
    fn a_constant_summand_moves_to_the_bound() {
        let shifted = apply(
            IntLess,
            vec![apply(IntSub, vec![variable("w"), int(1)]), int(0)],
        );
        let formula = read(&shifted).unwrap();
        assert_eq!(
            format!("{formula:?}"),
            format!("{:?}", super::bound("$1", super::Bound::Below, 1))
        );
    }
}
