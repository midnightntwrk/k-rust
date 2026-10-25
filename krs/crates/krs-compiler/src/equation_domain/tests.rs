//! The ground analysis of equations: the domain it enumerates, the overlap
//! it finds, and a property test of the enumeration against brute force.

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, ItemKind, NodeOrigin, PackageId, SemanticId,
    SourceMapKey, StableItemId,
};
use krs_ir_levels::{SemanticSortRef as Sort, SemanticTerm};

use std::collections::BTreeMap;

use super::{
    ColumnValues, Domain, EquationView, Evaluator, Ground, Undecided, ground_literal, guard_holds,
};
use crate::coverage::Signature;

use BuiltinOperation::{
    BoolAndThen, BoolNot, BoolOrElse, IntAdd, IntBitAnd, IntBitRange, IntEqual, IntGreater,
    IntGreaterEqual, IntLess, IntMul, IntNotEqual, IntSub, IntTDiv,
};

const INT: Sort = Sort::Builtin(BuiltinSort::Int);

/// An evaluator over no declarations: builtins only.
fn evaluator() -> &'static Evaluator<'static> {
    let signature: &'static Signature = Box::leak(Box::default());
    Box::leak(Box::new(Evaluator::new(signature)))
}
const BOOL: Sort = Sort::Builtin(BuiltinSort::Bool);

fn origin() -> NodeOrigin {
    NodeOrigin::new(
        SourceMapKey::new("sem.equation-domain").unwrap(),
        krs_ir::testing::authored(0, 1),
    )
}

fn item(name: &str) -> StableItemId {
    StableItemId::new(
        PackageId::new("EQUATIONS", "equations", "0.1.0", "test").unwrap(),
        ["fixture"],
        name,
        ItemKind::Constructor,
        "",
    )
    .unwrap()
}

fn variable(name: &str) -> SemanticTerm {
    SemanticTerm::variable(origin(), INT, SemanticId::new(name.to_owned()).unwrap())
}

fn int(value: i128) -> SemanticTerm {
    SemanticTerm::token(origin(), INT, value.to_string()).unwrap()
}

fn builtin(operation: BuiltinOperation, arguments: Vec<SemanticTerm>) -> SemanticTerm {
    let sort = Sort::Builtin(operation.result_sort().builtin().unwrap());
    SemanticTerm::application(
        origin(),
        sort,
        ApplicationRef::Builtin(operation),
        arguments,
    )
}

fn constructor(name: &str, arguments: Vec<SemanticTerm>) -> SemanticTerm {
    SemanticTerm::application(
        origin(),
        Sort::Builtin(BuiltinSort::KSequence),
        ApplicationRef::Declared(item(name)),
        arguments,
    )
}

fn all(conjuncts: Vec<SemanticTerm>) -> SemanticTerm {
    conjuncts
        .into_iter()
        .reduce(|left, right| builtin(BoolAndThen, vec![left, right]))
        .unwrap_or_else(|| SemanticTerm::token(origin(), BOOL, "true".to_owned()).unwrap())
}

/// The guard a `k::bits!` template on `subject` lowers to: the range, then
/// one `bitRangeInt` equality per maximal fixed run of each group.
fn template(subject: &str, text: &str) -> Vec<SemanticTerm> {
    let width = text.chars().filter(|c| *c != ' ').count();
    let mut guard = vec![
        builtin(IntGreaterEqual, vec![variable(subject), int(0)]),
        builtin(IntLess, vec![variable(subject), int(1 << width)]),
    ];
    // Bits from the least significant, each with its group.
    let mut bits = Vec::new();
    for (group, chunk) in text.split(' ').enumerate() {
        bits.extend(chunk.chars().map(|bit| (group, bit)));
    }
    bits.reverse();
    let mut offset = 0;
    while offset < bits.len() {
        let (group, bit) = bits[offset];
        if !matches!(bit, '0' | '1') {
            offset += 1;
            continue;
        }
        let start = offset;
        while offset < bits.len() && bits[offset].0 == group && matches!(bits[offset].1, '0' | '1')
        {
            offset += 1;
        }
        let value = bits[start..offset]
            .iter()
            .rev()
            .fold(0_i128, |value, (_, bit)| {
                value * 2 + i128::from(*bit == '1')
            });
        guard.push(builtin(
            IntEqual,
            vec![
                field(
                    subject,
                    i128::try_from(start).unwrap(),
                    i128::try_from(offset - start).unwrap(),
                ),
                int(value),
            ],
        ));
    }
    guard
}

fn field(subject: &str, offset: i128, length: i128) -> SemanticTerm {
    builtin(
        IntBitRange,
        vec![variable(subject), int(offset), int(length)],
    )
}

struct Equation {
    id: StableItemId,
    arguments: Vec<SemanticTerm>,
    guard: Option<SemanticTerm>,
    result: SemanticTerm,
}

fn equation(
    name: &str,
    arguments: Vec<SemanticTerm>,
    guard: Option<SemanticTerm>,
    result: SemanticTerm,
) -> Equation {
    Equation {
        id: item(name),
        arguments,
        guard,
        result,
    }
}

fn views(equations: &[Equation]) -> Vec<EquationView<'_>> {
    equations
        .iter()
        .map(|equation| EquationView {
            id: &equation.id,
            arguments: &equation.arguments,
            guard: equation.guard.as_ref(),
            result: &equation.result,
        })
        .collect()
}

/// The first point where two equations apply with different results.
fn overlap(columns: &[Sort], equations: &[Equation]) -> Option<(Vec<i128>, String, String)> {
    let views = views(equations);
    let domain = Domain::new(evaluator(), columns, &views)?;
    for point in domain.points() {
        let applying = (0..views.len())
            .filter(|index| domain.applies(*index, &point).unwrap())
            .collect::<Vec<_>>();
        for (position, first) in applying.iter().enumerate() {
            for second in &applying[position + 1..] {
                let left = domain.result(*first, &point).unwrap();
                let right = domain.result(*second, &point).unwrap();
                if left.0 != right.0 {
                    return Some((point, left.1, right.1));
                }
            }
        }
    }
    None
}

/// SM83's `LD r, r'` (`01 yyy zzz`) and HALT (`01 110 110`, the literal 118).
fn ld_and_halt(exclude_halt: bool) -> Vec<Equation> {
    let mut guard = template("op", "01 yyy zzz");
    if exclude_halt {
        guard.push(builtin(IntNotEqual, vec![variable("op"), int(118)]));
    }
    vec![
        equation(
            "decode_ld_r_r",
            vec![variable("op")],
            Some(all(guard)),
            constructor(
                "Ld",
                vec![
                    constructor("R8", vec![field("op", 3, 3)]),
                    constructor("R8", vec![field("op", 0, 3)]),
                ],
            ),
        ),
        equation(
            "decode_halt",
            vec![int(118)],
            None,
            constructor("Halt", Vec::new()),
        ),
    ]
}

#[test]
fn halt_overlaps_ld_unless_its_guard_excludes_it() {
    let (point, left, right) = overlap(&[INT], &ld_and_halt(false)).expect("an overlap");
    assert_eq!(point, [118]);
    assert_eq!(left, "Ld(R8(6), R8(6))");
    assert_eq!(right, "Halt");
    assert_eq!(overlap(&[INT], &ld_and_halt(true)), None);
}

#[test]
fn templates_that_differ_in_a_fixed_bit_do_not_overlap() {
    let equations = vec![
        equation(
            "inc",
            vec![variable("a")],
            Some(all(template("a", "00 yyy 100"))),
            constructor("Inc", vec![field("a", 3, 3)]),
        ),
        equation(
            "dec",
            vec![variable("b")],
            Some(all(template("b", "00 yyy 101"))),
            constructor("Dec", vec![field("b", 3, 3)]),
        ),
        equation("nop", vec![int(0)], None, constructor("Nop", Vec::new())),
    ];
    assert_eq!(overlap(&[INT], &equations), None);
    let views = views(&equations);
    let domain = Domain::new(evaluator(), &[INT], &views).unwrap();
    let ColumnValues::Int { values, bounded } = &domain.columns()[0] else {
        panic!("an Int column");
    };
    assert_eq!(
        (values.len(), values.last(), bounded.as_slice()),
        (257, Some(&256), &[(0, 256)][..])
    );
    // `inc` holds exactly on `00 yyy 100`.
    for point in domain.points() {
        let expected = (0..256).contains(&point[0]) && point[0] & 0b1100_0111 == 0b100;
        assert_eq!(domain.applies(0, &point).unwrap(), expected, "{point:?}");
    }
}

#[test]
fn equal_results_where_equations_overlap_are_no_overlap() {
    // `x` in 0..10 and `y` in 5..20, giving `x + 0` and `y`.
    let equations = vec![
        equation(
            "low",
            vec![variable("x")],
            Some(all(vec![
                builtin(IntGreaterEqual, vec![variable("x"), int(0)]),
                builtin(IntLess, vec![variable("x"), int(10)]),
            ])),
            builtin(BuiltinOperation::IntAdd, vec![variable("x"), int(0)]),
        ),
        equation(
            "high",
            vec![variable("y")],
            Some(all(vec![
                builtin(IntGreaterEqual, vec![variable("y"), int(5)]),
                builtin(IntLess, vec![variable("y"), int(20)]),
            ])),
            variable("y"),
        ),
    ];
    assert_eq!(overlap(&[INT], &equations), None);
}

#[test]
fn an_unbounded_or_unreadable_guard_is_beyond_the_analysis() {
    let unbounded = vec![equation(
        "positive",
        vec![variable("x")],
        Some(builtin(IntLess, vec![int(0), variable("x")])),
        int(1),
    )];
    assert!(Domain::new(evaluator(), &[INT], &views(&unbounded)).is_none());
    // Seventeen bits: more points than the analysis enumerates.
    let wide = vec![equation(
        "wide",
        vec![variable("x")],
        Some(all(template("x", "0________________"))),
        int(1),
    )];
    assert!(Domain::new(evaluator(), &[INT], &views(&wide)).is_none());
    // A guard that calls a function is not evaluated.
    let called = vec![equation(
        "called",
        vec![variable("x")],
        Some(all(vec![
            builtin(IntGreaterEqual, vec![variable("x"), int(0)]),
            builtin(IntLess, vec![variable("x"), int(4)]),
            builtin(
                IntEqual,
                vec![constructor("F", vec![variable("x")]), int(1)],
            ),
        ])),
        int(1),
    )];
    let views = views(&called);
    let domain = Domain::new(evaluator(), &[INT], &views).unwrap();
    assert!(matches!(domain.applies(0, &[1]), Err(Undecided)));
    // Outside the bound, a false top-level conjunct decides.
    assert!(matches!(domain.applies(0, &[4]), Ok(false)));
}

#[test]
fn an_undefined_guard_is_undecided_unless_a_conjunct_is_false() {
    // `x != 0 && 12 / x == 3` at 0 is false by its first conjunct;
    // `x == 0 || 12 / x == 3` at 0 is undefined in matching logic and true
    // on a short-circuiting backend: the analysis does not decide it.
    let range = || {
        vec![
            builtin(IntGreaterEqual, vec![variable("x"), int(0)]),
            builtin(IntLess, vec![variable("x"), int(8)]),
        ]
    };
    let quotient = || {
        builtin(
            IntEqual,
            vec![builtin(IntTDiv, vec![int(12), variable("x")]), int(3)],
        )
    };
    let mut guarded = range();
    guarded.push(builtin(IntNotEqual, vec![variable("x"), int(0)]));
    guarded.push(quotient());
    let mut either = range();
    either.push(builtin(
        BoolOrElse,
        vec![builtin(IntEqual, vec![variable("x"), int(0)]), quotient()],
    ));
    let equations = vec![
        equation("guarded", vec![variable("x")], Some(all(guarded)), int(1)),
        equation("either", vec![variable("x")], Some(all(either)), int(1)),
    ];
    let views = views(&equations);
    let domain = Domain::new(evaluator(), &[INT], &views).unwrap();
    assert!(matches!(domain.applies(0, &[0]), Ok(false)));
    assert!(matches!(domain.applies(0, &[4]), Ok(true)));
    assert!(matches!(domain.applies(1, &[0]), Err(Undecided)));
    assert!(matches!(domain.applies(1, &[4]), Ok(true)));
    assert!(matches!(domain.applies(1, &[5]), Ok(false)));
}

// ---------------------------------------------------------------------------
// The enumeration against brute force

/// A small deterministic generator (xorshift64*).
struct Random(u64);

impl Random {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, bound: u64) -> i128 {
        i128::from(self.next() % bound)
    }
}

/// One random argument pattern and the conjuncts it adds to the guard, with
/// a brute-force reading.
enum Spec {
    Literal(i128),
    /// A binder the guard does not read.
    Free,
    /// A binder bounded to `low..high`, with a bit run `(offset, length,
    /// value)` and an excluded value.
    Bounded {
        low: i128,
        high: i128,
        run: Option<(i128, i128, i128)>,
        excluded: Option<i128>,
    },
}

impl Spec {
    fn random(random: &mut Random) -> Self {
        match random.below(4) {
            0 => Self::Literal(random.below(12) - 2),
            1 => Self::Free,
            _ => {
                let low = random.below(10) - 3;
                let high = low + random.below(14);
                let run = (random.below(2) == 0).then(|| {
                    let length = 1 + random.below(2);
                    (random.below(3), length, random.below(1 << length))
                });
                let excluded = (random.below(2) == 0).then(|| random.below(14) - 2);
                Self::Bounded {
                    low,
                    high,
                    run,
                    excluded,
                }
            }
        }
    }

    fn admits(&self, value: i128) -> bool {
        match self {
            Self::Literal(literal) => value == *literal,
            Self::Free => true,
            Self::Bounded {
                low,
                high,
                run,
                excluded,
            } => {
                *low <= value
                    && value < *high
                    && run.is_none_or(|(offset, length, bits)| {
                        (value >> offset).rem_euclid(1 << length) == bits
                    })
                    && excluded.is_none_or(|excluded| value != excluded)
            }
        }
    }

    /// The pattern and guard conjuncts of the binder `name`.
    fn terms(&self, name: &str) -> (SemanticTerm, Vec<SemanticTerm>) {
        match self {
            Self::Literal(literal) => (int(*literal), Vec::new()),
            Self::Free => (variable(name), Vec::new()),
            Self::Bounded {
                low,
                high,
                run,
                excluded,
            } => {
                let mut guard = vec![
                    builtin(IntLess, vec![int(*low - 1), variable(name)]),
                    builtin(IntLess, vec![variable(name), int(*high)]),
                ];
                if let Some((offset, length, bits)) = run {
                    guard.push(builtin(
                        IntEqual,
                        vec![field(name, *offset, *length), int(*bits)],
                    ));
                }
                if let Some(excluded) = excluded {
                    guard.push(builtin(IntNotEqual, vec![variable(name), int(*excluded)]));
                }
                (variable(name), guard)
            }
        }
    }
}

#[test]
fn the_enumeration_decides_every_argument_as_brute_force_does() {
    let mut random = Random(0x5EED_0FB1_7500_0001);
    let mut checked = 0_usize;
    for _ in 0..300 {
        let count = 1 + usize::try_from(random.below(4)).unwrap();
        let specs = (0..count)
            .map(|_| [Spec::random(&mut random), Spec::random(&mut random)])
            .collect::<Vec<_>>();
        let equations = specs
            .iter()
            .enumerate()
            .map(|(index, [first, second])| {
                let (left, mut guard) = first.terms(&format!("x{index}"));
                let (right, more) = second.terms(&format!("y{index}"));
                guard.extend(more);
                equation(
                    &format!("e{index}"),
                    vec![left, right],
                    (!guard.is_empty()).then(|| all(guard)),
                    int(0),
                )
            })
            .collect::<Vec<_>>();
        let views = views(&equations);
        let domain =
            Domain::new(evaluator(), &[INT, INT], &views).expect("small domains are enumerated");
        // Each coordinate stands for itself when the domain lists it, and
        // otherwise for `outside`.
        let representative = |column: usize, value: i128| match &domain.columns()[column] {
            ColumnValues::Int { values, bounded } => {
                if values.contains(&value) {
                    value
                } else {
                    // The one listed value outside the bounded intervals.
                    *values
                        .iter()
                        .find(|listed| {
                            !bounded
                                .iter()
                                .any(|(low, high)| low <= *listed && *listed < high)
                        })
                        .unwrap()
                }
            }
            ColumnValues::Free => unreachable!("Int columns"),
        };
        for x in -20..30 {
            for y in -20..30 {
                let point = [representative(0, x), representative(1, y)];
                for (index, [first, second]) in specs.iter().enumerate() {
                    let brute = first.admits(x) && second.admits(y);
                    let enumerated = domain.applies(index, &point).unwrap();
                    assert_eq!(
                        brute, enumerated,
                        "equation {index} at ({x}, {y}), represented by {point:?}"
                    );
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 500_000, "{checked}");
}

// ---------------------------------------------------------------------------
// Total functions evaluated by their own equations

fn call(name: &str, arguments: Vec<SemanticTerm>) -> SemanticTerm {
    SemanticTerm::application(
        origin(),
        INT,
        ApplicationRef::Declared(item(name)),
        arguments,
    )
}

/// An evaluator that applies each function by `equations`, given by name
/// with each equation's priority.
fn functions(equations: &[(&str, u32, &Equation)]) -> &'static Evaluator<'static> {
    let signature: &'static Signature = Box::leak(Box::default());
    let mut bands =
        BTreeMap::<&'static StableItemId, BTreeMap<u32, Vec<EquationView<'static>>>>::new();
    for (name, priority, equation) in equations {
        let equation: &'static Equation = Box::leak(Box::new(Equation {
            id: equation.id.clone(),
            arguments: equation.arguments.clone(),
            guard: equation.guard.clone(),
            result: equation.result.clone(),
        }));
        let id: &'static StableItemId = Box::leak(Box::new(item(name)));
        let view = EquationView {
            id: &equation.id,
            arguments: &equation.arguments,
            guard: equation.guard.as_ref(),
            result: &equation.result,
        };
        bands
            .entry(id)
            .or_default()
            .entry(*priority)
            .or_default()
            .push(view);
    }
    Box::leak(Box::new(Evaluator::with_functions(
        signature,
        bands
            .into_iter()
            .map(|(id, bands)| (id, bands.into_values().collect()))
            .collect(),
    )))
}

/// The value of `name(arguments)`, or `None` when the evaluator gives up.
fn value_of(evaluator: &Evaluator<'_>, name: &str, arguments: &[i128]) -> Option<String> {
    ground_literal(
        evaluator,
        &call(
            name,
            arguments.iter().map(|argument| int(*argument)).collect(),
        ),
        &BTreeMap::new(),
    )
}

/// `sign(v) => 1 requires v >= 0` and `sign(v) => -1 requires not (v >= 0)`.
fn sign() -> Vec<Equation> {
    let nonnegative = || builtin(IntGreaterEqual, vec![variable("v"), int(0)]);
    vec![
        equation("sign_1", vec![variable("v")], Some(nonnegative()), int(1)),
        equation(
            "sign_2",
            vec![variable("v")],
            Some(builtin(BoolNot, vec![nonnegative()])),
            int(-1),
        ),
    ]
}

#[test]
fn a_total_function_evaluates_by_its_own_equations() {
    let sign = sign();
    let evaluator = functions(&[("sign", 50, &sign[0]), ("sign", 50, &sign[1])]);
    assert_eq!(value_of(evaluator, "sign", &[5]).as_deref(), Some("1"));
    assert_eq!(value_of(evaluator, "sign", &[0]).as_deref(), Some("1"));
    assert_eq!(value_of(evaluator, "sign", &[-5]).as_deref(), Some("-1"));
    // A guard that applies it.
    let guard = builtin(IntEqual, vec![call("sign", vec![variable("x")]), int(1)]);
    let x = SemanticId::new("x".to_owned()).unwrap();
    let at = |value: i128| BTreeMap::from([(&x, Ground::Int(value))]);
    assert_eq!(guard_holds(evaluator, &guard, &at(3)), Some(true));
    assert_eq!(guard_holds(evaluator, &guard, &at(-3)), Some(false));
    // A function the evaluator does not hold decides nothing.
    assert_eq!(value_of(evaluator, "other", &[5]), None);
}

#[test]
fn the_first_priority_band_that_applies_gives_the_value() {
    // `pick(0) => 10`, and `pick(_) => 20` as `owise`.
    let zero = equation("pick_zero", vec![int(0)], None, int(10));
    let other = equation("pick_other", vec![variable("v")], None, int(20));
    let evaluator = functions(&[("pick", 50, &zero), ("pick", 200, &other)]);
    assert_eq!(value_of(evaluator, "pick", &[0]).as_deref(), Some("10"));
    assert_eq!(value_of(evaluator, "pick", &[1]).as_deref(), Some("20"));
}

#[test]
fn the_evaluator_gives_up_rather_than_guess() {
    // No equation applies to 1.
    let only_zero = equation("only_zero", vec![int(0)], None, int(1));
    // Two equations at one priority that disagree on 0, and agree on 1.
    let first = equation(
        "first",
        vec![variable("v")],
        None,
        builtin(IntMul, vec![variable("v"), int(2)]),
    );
    let second = equation("second", vec![variable("v")], None, variable("v"));
    // `forever(v) => forever(v)`, and `count(0) => 0`, `count(n) => count(n - 1) + 1`.
    let forever = equation(
        "forever",
        vec![variable("v")],
        None,
        call("forever", vec![variable("v")]),
    );
    let count_zero = equation("count_zero", vec![int(0)], None, int(0));
    let count_more = equation(
        "count_more",
        vec![variable("n")],
        Some(builtin(IntGreater, vec![variable("n"), int(0)])),
        builtin(
            IntAdd,
            vec![
                call("count", vec![builtin(IntSub, vec![variable("n"), int(1)])]),
                int(1),
            ],
        ),
    );
    // A guard undefined at 0, where a lazy and a strict reading disagree.
    let undefined = equation(
        "undefined",
        vec![variable("v")],
        Some(builtin(
            BoolOrElse,
            vec![
                builtin(IntEqual, vec![variable("v"), int(0)]),
                builtin(
                    IntGreater,
                    vec![builtin(IntTDiv, vec![int(1), variable("v")]), int(0)],
                ),
            ],
        )),
        int(1),
    );
    let calls_unknown = equation(
        "calls_unknown",
        vec![variable("v")],
        None,
        call("unknown", vec![variable("v")]),
    );
    let evaluator = functions(&[
        ("only_zero", 50, &only_zero),
        ("twice", 50, &first),
        ("twice", 50, &second),
        ("forever", 50, &forever),
        ("count", 50, &count_zero),
        ("count", 50, &count_more),
        ("undefined", 50, &undefined),
        ("calls_unknown", 50, &calls_unknown),
    ]);
    assert_eq!(value_of(evaluator, "only_zero", &[0]).as_deref(), Some("1"));
    assert_eq!(value_of(evaluator, "only_zero", &[1]), None);
    assert_eq!(value_of(evaluator, "twice", &[0]).as_deref(), Some("0"));
    assert_eq!(value_of(evaluator, "twice", &[1]), None);
    assert_eq!(value_of(evaluator, "forever", &[1]), None);
    assert_eq!(value_of(evaluator, "count", &[10]).as_deref(), Some("10"));
    // Deeper than the call depth.
    assert_eq!(value_of(evaluator, "count", &[1000]), None);
    assert_eq!(value_of(evaluator, "undefined", &[0]), None);
    assert_eq!(value_of(evaluator, "undefined", &[1]).as_deref(), Some("1"));
    assert_eq!(value_of(evaluator, "calls_unknown", &[1]), None);
}

#[test]
fn the_ground_analysis_evaluates_function_guards() {
    // `low(v) => v &Int 3`, and `pick(op)` on `0 <= op < 8` by `low(op)`.
    let low = equation(
        "low",
        vec![variable("v")],
        None,
        builtin(IntBitAnd, vec![variable("v"), int(3)]),
    );
    let evaluator = functions(&[("low", 50, &low)]);
    let row = |name: &str, value: i128| {
        let mut guard = vec![
            builtin(IntGreaterEqual, vec![variable("op"), int(0)]),
            builtin(IntLess, vec![variable("op"), int(8)]),
        ];
        guard.push(builtin(
            IntEqual,
            vec![call("low", vec![variable("op")]), int(value)],
        ));
        equation(name, vec![variable("op")], Some(all(guard)), int(value))
    };
    let equations = [row("pick_0", 0), row("pick_1", 1), row("pick_2", 2)];
    let views = views(&equations);
    let domain = Domain::new(evaluator, &[INT], &views).unwrap();
    let uncovered = domain
        .points()
        .filter(|point| (0..views.len()).all(|index| !domain.applies(index, point).unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(uncovered, [vec![3], vec![7], vec![8]]);
}
