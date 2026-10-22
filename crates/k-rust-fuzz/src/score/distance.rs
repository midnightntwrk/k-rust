//! The branch-distance algebra of ARCHITECTURE 6.2 over a condition tree of the crate's own
//! ([`Cond`]), so that the shape of the backend's condition records is read in one place
//! (`super::records`).
//!
//! # Why the distance ranks inputs
//!
//! A rule's `requires` is a Boolean term over the matched instance. For an input on which it is
//! false, the distance measures how far the instance is from making it true: 0 exactly when the
//! condition holds, and smaller the fewer and the smaller the changes of operand values it needs.
//!
//! - An integer comparison is the distance between its operands on the number line: `a ==Int b`
//!   needs `|a - b|` unit moves of one operand, `a <Int b` needs `a - b + 1` when it is false,
//!   and `a <=Int b` needs `a - b`. Their negations are comparisons too (`=/=Int`, `>=Int`,
//!   `>Int`), so a negation is pushed inward instead of being read as "false or not".
//! - String equality is the edit work after the common prefix: the length difference plus the
//!   characters of the shorter string from the first differing position on (0 exactly when the
//!   strings are equal; a longer common prefix is nearer).
//! - Any other atom is 0 when true and 1 when false: it states no order on its operands.
//! - A conjunction holds when every conjunct holds, so its distance is the sum; a disjunction
//!   holds when one disjunct holds, so its distance is the least; `a impliesBool b` is
//!   `notBool a orBool b`. Negation is pushed inward by De Morgan's laws.
//! - Each atom's distance `d` is normalized to `d / (d + 1)` before it is summed, so that one
//!   atom's large distance does not drown another atom's (the normalization keeps the order
//!   within an atom, and every normalized distance is below 1).
//!
//! The distance is defined only when every atom has a truth value from ground operands. An atom
//! whose operands are symbolic, undefined, omitted or unevaluated, or whose truth the record
//! leaves undecided, gives no distance, and then neither does the condition: such an atom is no
//! signal, never a distance of 0 (an undecided atom is not a satisfied one).
//!
//! Distances are exact fractions, so that two distances compare correctly at any magnitude: a
//! guard such as `x >Int 2^70` ranks `2^69` above `2^68`, which a fixed-point rendering of
//! `d / (d + 1)` would not separate.

use std::cmp::Ordering;

use num_bigint::{BigInt, BigUint};
use num_traits::{One as _, Zero as _};

/// A ground operand of a comparison atom.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Operand {
    /// An `Int` value.
    Int(BigInt),
    /// A `String` value, as Unicode scalar values.
    Str(String),
}

/// The comparisons the algebra measures by their operands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Comparison {
    /// `==Int` (and `==K`, `\equals` of two integers).
    IntEq,
    /// `=/=Int` (and `=/=K` of two integers).
    IntNe,
    /// `<Int`.
    IntLt,
    /// `<=Int`.
    IntLe,
    /// `>Int`.
    IntGt,
    /// `>=Int`.
    IntGe,
    /// `==String` (and `==K`, `\equals` of two strings).
    StrEq,
    /// `=/=String` (and `=/=K` of two strings).
    StrNe,
}

impl Comparison {
    /// The comparison that holds exactly when this one does not.
    pub(crate) fn negated(self) -> Self {
        match self {
            Self::IntEq => Self::IntNe,
            Self::IntNe => Self::IntEq,
            Self::IntLt => Self::IntGe,
            Self::IntLe => Self::IntGt,
            Self::IntGt => Self::IntLe,
            Self::IntGe => Self::IntLt,
            Self::StrEq => Self::StrNe,
            Self::StrNe => Self::StrEq,
        }
    }
}

/// The truth of an atom the algebra does not measure by its operands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Truth {
    /// The atom holds.
    True,
    /// The atom does not hold.
    False,
    /// No truth value: undefined, undecided, or over operands that are not ground values.
    Unknown,
}

/// A condition as the algebra reads it: Boolean connectives over atoms.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Cond {
    /// Every child holds (an empty conjunction holds).
    And(Vec<Cond>),
    /// Some child holds (an empty disjunction does not hold).
    Or(Vec<Cond>),
    /// The child does not hold.
    Not(Box<Cond>),
    /// The first child does not hold, or the second holds.
    Implies(Box<Cond>, Box<Cond>),
    /// A comparison of two ground operands; `None` when an operand is not a ground value of the
    /// comparison's sort, which gives no distance.
    Compare(Comparison, Option<(Operand, Operand)>),
    /// Any other atom, by its truth.
    Atom(Truth),
    /// A node whose truth an evaluation already decided: a node that holds has distance 0 and
    /// its negation is measured from `cond`; a node that does not hold is measured from `cond`
    /// and its negation has distance 0; a node without a truth value (undefined, undecided)
    /// gives no distance either way.
    Decided(Truth, Box<Cond>),
}

/// A non-negative exact fraction: a sum of normalized atom distances. Ordered by value.
#[derive(Clone, Debug)]
pub(crate) struct Distance {
    numerator: BigUint,
    denominator: BigUint,
}

impl Distance {
    /// The distance of a condition that holds.
    pub(crate) fn zero() -> Self {
        Self {
            numerator: BigUint::zero(),
            denominator: BigUint::one(),
        }
    }

    /// Whether this is the distance of a condition that holds.
    pub(crate) fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }

    /// The normalized distance `d / (d + 1)` of an atom whose raw distance is `raw`.
    pub(crate) fn normalized(raw: BigUint) -> Self {
        let denominator = &raw + 1u8;
        Self {
            numerator: raw,
            denominator,
        }
    }

    fn add(&self, other: &Self) -> Self {
        Self {
            numerator: &self.numerator * &other.denominator + &other.numerator * &self.denominator,
            denominator: &self.denominator * &other.denominator,
        }
    }

    /// The fraction as `(numerator, denominator)` in lowest terms.
    #[cfg(test)]
    pub(crate) fn parts(&self) -> (BigUint, BigUint) {
        let (mut a, mut b) = (self.numerator.clone(), self.denominator.clone());
        while !b.is_zero() {
            let rest = &a % &b;
            a = b;
            b = rest;
        }
        let divisor = a;
        (&self.numerator / &divisor, &self.denominator / &divisor)
    }
}

impl Ord for Distance {
    fn cmp(&self, other: &Self) -> Ordering {
        (&self.numerator * &other.denominator).cmp(&(&other.numerator * &self.denominator))
    }
}

impl PartialOrd for Distance {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Distance {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Distance {}

/// The distance of `cond` (module documentation), or `None` when some atom gives no distance.
pub(crate) fn distance(cond: &Cond) -> Option<Distance> {
    distance_with(cond, true)
}

/// The distance of `cond` when `positive`, and of its negation otherwise.
fn distance_with(cond: &Cond, positive: bool) -> Option<Distance> {
    match cond {
        Cond::And(children) if positive => sum(children, true),
        Cond::And(children) => least(children, false),
        Cond::Or(children) if positive => least(children, true),
        Cond::Or(children) => sum(children, false),
        Cond::Not(child) => distance_with(child, !positive),
        Cond::Implies(antecedent, consequent) => {
            // `a => b` is `not a or b`; its negation is `a and not b`.
            let antecedent = distance_with(antecedent, !positive)?;
            let consequent = distance_with(consequent, positive)?;
            Some(if positive {
                antecedent.min(consequent)
            } else {
                antecedent.add(&consequent)
            })
        }
        Cond::Compare(comparison, operands) => {
            let comparison = if positive {
                *comparison
            } else {
                comparison.negated()
            };
            let (left, right) = operands.as_ref()?;
            raw_comparison(comparison, left, right).map(Distance::normalized)
        }
        Cond::Decided(truth, cond) => match (truth, positive) {
            (Truth::Unknown, _) => None,
            (Truth::True, true) | (Truth::False, false) => Some(Distance::zero()),
            (Truth::True, false) | (Truth::False, true) => distance_with(cond, positive),
        },
        Cond::Atom(truth) => match (truth, positive) {
            (Truth::Unknown, _) => None,
            (Truth::True, true) | (Truth::False, false) => Some(Distance::zero()),
            (Truth::True, false) | (Truth::False, true) => {
                Some(Distance::normalized(BigUint::one()))
            }
        },
    }
}

/// The sum of the children's distances (each of their negations when not `positive`); `None`
/// when one gives none. An empty sum is 0.
fn sum(children: &[Cond], positive: bool) -> Option<Distance> {
    let mut total = Distance::zero();
    for child in children {
        total = total.add(&distance_with(child, positive)?);
    }
    Some(total)
}

/// The least of the children's distances (each of their negations when not `positive`); `None`
/// when one gives none, since the condition is defined only when every atom is. An empty
/// disjunction does not hold: distance 1.
fn least(children: &[Cond], positive: bool) -> Option<Distance> {
    let mut best: Option<Distance> = None;
    for child in children {
        let distance = distance_with(child, positive)?;
        best = Some(match best {
            Some(best) => best.min(distance),
            None => distance,
        });
    }
    Some(best.unwrap_or_else(|| Distance::normalized(BigUint::one())))
}

/// The raw (unnormalized) distance of `comparison` over `left` and `right`; `None` when the
/// operands are not of the comparison's sort.
fn raw_comparison(comparison: Comparison, left: &Operand, right: &Operand) -> Option<BigUint> {
    let positive = |value: BigInt| value.to_biguint().unwrap_or_default();
    let flag = |holds: bool| {
        if holds {
            BigUint::zero()
        } else {
            BigUint::one()
        }
    };
    match (comparison, left, right) {
        (Comparison::IntEq, Operand::Int(a), Operand::Int(b)) => Some((a - b).magnitude().clone()),
        (Comparison::IntNe, Operand::Int(a), Operand::Int(b)) => Some(flag(a != b)),
        (Comparison::IntLt, Operand::Int(a), Operand::Int(b)) => Some(positive(a - b + 1)),
        (Comparison::IntLe, Operand::Int(a), Operand::Int(b)) => Some(positive(a - b)),
        (Comparison::IntGt, Operand::Int(a), Operand::Int(b)) => Some(positive(b - a + 1)),
        (Comparison::IntGe, Operand::Int(a), Operand::Int(b)) => Some(positive(b - a)),
        (Comparison::StrEq, Operand::Str(a), Operand::Str(b)) => Some(string_distance(a, b)),
        (Comparison::StrNe, Operand::Str(a), Operand::Str(b)) => Some(flag(a != b)),
        _ => None,
    }
}

/// The distance of `a ==String b`: the length difference plus the characters of the shorter
/// string from the first position where the two differ (module documentation).
fn string_distance(a: &str, b: &str) -> BigUint {
    let (a, b): (Vec<char>, Vec<char>) = (a.chars().collect(), b.chars().collect());
    let shorter = a.len().min(b.len());
    let common = a.iter().zip(&b).take_while(|(x, y)| x == y).count();
    BigUint::from(a.len().abs_diff(b.len())) + BigUint::from(shorter - common)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(value: i64) -> Operand {
        Operand::Int(BigInt::from(value))
    }

    fn compare(comparison: Comparison, a: i64, b: i64) -> Cond {
        Cond::Compare(comparison, Some((int(a), int(b))))
    }

    fn string(comparison: Comparison, a: &str, b: &str) -> Cond {
        Cond::Compare(
            comparison,
            Some((Operand::Str(a.into()), Operand::Str(b.into()))),
        )
    }

    /// `d / (d + 1)` in lowest terms, as `(numerator, denominator)`.
    fn parts(cond: &Cond) -> (u64, u64) {
        let (numerator, denominator) = distance(cond).expect("a distance").parts();
        (
            u64::try_from(numerator).expect("small"),
            u64::try_from(denominator).expect("small"),
        )
    }

    fn not(cond: Cond) -> Cond {
        Cond::Not(Box::new(cond))
    }

    #[test]
    fn integer_equality_is_the_normalized_gap() {
        assert_eq!(parts(&compare(Comparison::IntEq, 7, 7)), (0, 1));
        assert_eq!(parts(&compare(Comparison::IntEq, 3, 7)), (4, 5));
        assert_eq!(parts(&compare(Comparison::IntEq, 7, -3)), (10, 11));
        // `=/=Int` is 0 or 1 before normalization.
        assert_eq!(parts(&compare(Comparison::IntNe, 3, 7)), (0, 1));
        assert_eq!(parts(&compare(Comparison::IntNe, 7, 7)), (1, 2));
    }

    #[test]
    fn strict_and_weak_orders_measure_the_missing_steps() {
        // a < b needs a - b + 1 when false.
        assert_eq!(parts(&compare(Comparison::IntLt, 3, 7)), (0, 1));
        assert_eq!(parts(&compare(Comparison::IntLt, 7, 7)), (1, 2));
        assert_eq!(parts(&compare(Comparison::IntLt, 10, 7)), (4, 5));
        // a <= b needs a - b.
        assert_eq!(parts(&compare(Comparison::IntLe, 7, 7)), (0, 1));
        assert_eq!(parts(&compare(Comparison::IntLe, 10, 7)), (3, 4));
        // a > b is b < a; a >= b is b <= a.
        assert_eq!(parts(&compare(Comparison::IntGt, 1000, 1000)), (1, 2));
        assert_eq!(parts(&compare(Comparison::IntGt, -3, 1000)), (1004, 1005));
        assert_eq!(parts(&compare(Comparison::IntGe, 999, 1000)), (1, 2));
    }

    #[test]
    fn a_smaller_gap_is_nearer_at_any_magnitude() {
        let big = |exponent: u32| Operand::Int(BigInt::from(2u8).pow(exponent));
        let gt = |exponent: u32| {
            distance(&Cond::Compare(
                Comparison::IntGt,
                Some((big(exponent), big(70))),
            ))
            .expect("a distance")
        };
        assert!(gt(69) < gt(68));
        assert!(gt(68) < gt(2));
    }

    #[test]
    fn conjunction_sums_and_disjunction_takes_the_least() {
        // 1000 < D < 1100 at D = -3: (1004/1005) + 0.
        let window = Cond::And(vec![
            compare(Comparison::IntGt, -3, 1000),
            compare(Comparison::IntLt, -3, 1100),
        ]);
        assert_eq!(parts(&window), (1004, 1005));
        // x == 3 and y == 5 at (4, 7): 1/2 + 2/3.
        let both = Cond::And(vec![
            compare(Comparison::IntEq, 4, 3),
            compare(Comparison::IntEq, 7, 5),
        ]);
        assert_eq!(parts(&both), (7, 6));
        let either = Cond::Or(vec![
            compare(Comparison::IntEq, 4, 3),
            compare(Comparison::IntEq, 7, 5),
        ]);
        assert_eq!(parts(&either), (1, 2));
        // Empty connectives: `true` and `false`.
        assert_eq!(parts(&Cond::And(Vec::new())), (0, 1));
        assert_eq!(parts(&Cond::Or(Vec::new())), (1, 2));
    }

    #[test]
    fn negation_is_pushed_inward() {
        // not (x == 3) at x = 3 is x =/= 3: 1/2; at 4: 0.
        assert_eq!(parts(&not(compare(Comparison::IntEq, 3, 3))), (1, 2));
        assert_eq!(parts(&not(compare(Comparison::IntEq, 4, 3))), (0, 1));
        // not (x < 5) is x >= 5: at 2, 3 steps.
        assert_eq!(parts(&not(compare(Comparison::IntLt, 2, 5))), (3, 4));
        // not (x <= 5) is x > 5: at 5, one step.
        assert_eq!(parts(&not(compare(Comparison::IntLe, 5, 5))), (1, 2));
        // not (a and b) = not a or not b: the least; not (a or b) = not a and not b: the sum.
        let a = compare(Comparison::IntEq, 1, 1);
        let b = compare(Comparison::IntEq, 2, 2);
        assert_eq!(parts(&not(Cond::And(vec![a.clone(), b.clone()]))), (1, 2));
        assert_eq!(parts(&not(Cond::Or(vec![a.clone(), b]))), (1, 1));
        // Double negation.
        assert_eq!(parts(&not(not(compare(Comparison::IntEq, 3, 7)))), (4, 5));
        // Other atoms: true is 0, false 1/2, and their negations swap.
        assert_eq!(parts(&not(Cond::Atom(Truth::True))), (1, 2));
        assert_eq!(parts(&not(Cond::Atom(Truth::False))), (0, 1));
    }

    #[test]
    fn implication_is_not_antecedent_or_consequent() {
        let implies = |a: Cond, b: Cond| Cond::Implies(Box::new(a), Box::new(b));
        // A false antecedent satisfies the implication.
        assert_eq!(
            parts(&implies(
                compare(Comparison::IntEq, 1, 2),
                compare(Comparison::IntEq, 5, 9)
            )),
            (0, 1)
        );
        // A true antecedent leaves the consequent's distance, or the antecedent's negation's
        // (1/2 for an equality that holds), whichever is less.
        assert_eq!(
            parts(&implies(
                compare(Comparison::IntEq, 1, 1),
                compare(Comparison::IntEq, 5, 9)
            )),
            (1, 2)
        );
        assert_eq!(
            parts(&implies(
                compare(Comparison::IntLt, 1, 5),
                compare(Comparison::IntLt, 6, 5)
            )),
            (2, 3)
        );
        // not (a => b) = a and not b.
        assert_eq!(
            parts(&not(implies(
                compare(Comparison::IntEq, 3, 7),
                compare(Comparison::IntEq, 5, 5)
            ))),
            (4 * 2 + 5, 5 * 2)
        );
    }

    #[test]
    fn string_equality_is_the_work_after_the_common_prefix() {
        assert_eq!(parts(&string(Comparison::StrEq, "open", "open")), (0, 1));
        // "opal" against "open": common prefix 2, 2 characters to change.
        assert_eq!(parts(&string(Comparison::StrEq, "opal", "open")), (2, 3));
        // "op" against "open": 2 characters missing.
        assert_eq!(parts(&string(Comparison::StrEq, "op", "open")), (2, 3));
        // "shut" against "open": nothing shared.
        assert_eq!(parts(&string(Comparison::StrEq, "shut", "open")), (4, 5));
        assert_eq!(parts(&string(Comparison::StrNe, "a", "a")), (1, 2));
        // A longer common prefix is nearer.
        let near = distance(&string(Comparison::StrEq, "opex", "open"));
        let far = distance(&string(Comparison::StrEq, "oxxx", "open"));
        assert!(near < far);
    }

    #[test]
    fn a_decided_node_is_measured_only_where_it_fails() {
        let decided = |truth, cond: Cond| Cond::Decided(truth, Box::new(cond));
        // A node that holds is at distance 0 without its children being measured (an unknown
        // child below a decided node does not make it undefined).
        let holds = decided(
            Truth::True,
            Cond::Or(vec![
                compare(Comparison::IntEq, 1, 1),
                Cond::Atom(Truth::Unknown),
            ]),
        );
        assert_eq!(parts(&holds), (0, 1));
        // Its negation is measured from the children.
        assert_eq!(distance(&not(holds)), None);
        let fails = decided(Truth::False, compare(Comparison::IntEq, 3, 7));
        assert_eq!(parts(&fails), (4, 5));
        assert_eq!(parts(&not(fails)), (0, 1));
        // An undefined or undecided node gives no distance either way.
        let unknown = decided(Truth::Unknown, compare(Comparison::IntEq, 3, 7));
        assert_eq!(distance(&unknown), None);
        assert_eq!(distance(&not(unknown)), None);
    }

    #[test]
    fn an_atom_without_a_truth_value_gives_no_distance_never_zero() {
        assert_eq!(distance(&Cond::Atom(Truth::Unknown)), None);
        assert_eq!(distance(&Cond::Compare(Comparison::IntEq, None)), None);
        // Mismatched operand sorts are no signal either.
        assert_eq!(
            distance(&Cond::Compare(
                Comparison::IntEq,
                Some((int(1), Operand::Str("1".into())))
            )),
            None
        );
        // One unknown atom makes the whole condition undefined, under every connective, even
        // where the other atoms decide it.
        let unknown = Cond::Atom(Truth::Unknown);
        let holds = compare(Comparison::IntEq, 1, 1);
        assert_eq!(
            distance(&Cond::And(vec![holds.clone(), unknown.clone()])),
            None
        );
        assert_eq!(
            distance(&Cond::Or(vec![holds.clone(), unknown.clone()])),
            None
        );
        assert_eq!(distance(&not(unknown.clone())), None);
        assert_eq!(
            distance(&Cond::Implies(Box::new(unknown), Box::new(holds))),
            None
        );
    }
}
