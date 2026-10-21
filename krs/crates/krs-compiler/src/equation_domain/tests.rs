//! The ground analysis of equations: the domain it enumerates, the overlap
//! it finds, and a property test of the enumeration against brute force.

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, ItemKind, NodeOrigin, PackageId, SemanticId,
    SourceMapKey, StableItemId,
};
use krs_ir_levels::{SemanticSortRef as Sort, SemanticTerm};

use super::{ColumnValues, Domain, EquationView, Undecided};

use BuiltinOperation::{
    BoolAndThen, BoolOrElse, IntBitRange, IntEqual, IntGreaterEqual, IntLess, IntNotEqual, IntTDiv,
};

const INT: Sort = Sort::Builtin(BuiltinSort::Int);
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
    let domain = Domain::new(columns, &views)?;
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
    let domain = Domain::new(&[INT], &views).unwrap();
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
    assert!(Domain::new(&[INT], &views(&unbounded)).is_none());
    // Seventeen bits: more points than the analysis enumerates.
    let wide = vec![equation(
        "wide",
        vec![variable("x")],
        Some(all(template("x", "0________________"))),
        int(1),
    )];
    assert!(Domain::new(&[INT], &views(&wide)).is_none());
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
    let domain = Domain::new(&[INT], &views).unwrap();
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
    let domain = Domain::new(&[INT], &views).unwrap();
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
        let domain = Domain::new(&[INT, INT], &views).expect("small domains are enumerated");
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
