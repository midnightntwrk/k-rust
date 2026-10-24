//! The condition reader against the meaning of its atoms: a unit test per comparison identity and
//! per atom true wherever defined, and a property test that compares `contradictory` and
//! `equalities` with brute force over integer assignments (the design's "Revision after review 1",
//! R1.7).

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use super::{contradictory, equalities, equalities_with_bounds, literal_values};
use crate::{
    definition::BackendDefinition,
    rule::Predicate,
    term::{Term, TermKind},
};

const DEFINITION: &str = r#"
[] module MAIN
    hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
    sort SortMyTok{} [hasDomainValues{}(), token{}()]
    hooked-sort SortMyBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
    hooked-symbol ltInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.lt")]
    hooked-symbol leInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.le")]
    hooked-symbol gtInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.gt")]
    hooked-symbol geInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.ge")]
    hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.eq")]
    hooked-symbol neInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.ne")]
    hooked-symbol notBool{}(SortBool{}) : SortBool{} [function{}(), total{}(), hook{}("BOOL.not")]
    hooked-symbol addInt{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}(), hook{}("INT.add")]
    hooked-symbol subInt{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}(), hook{}("INT.sub")]
    hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), hook{}("INT.tdiv")]
    hooked-symbol absInt{}(SortInt{}) : SortInt{} [function{}(), total{}(), hook{}("INT.abs")]
    hooked-symbol minInt{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}(), hook{}("INT.min")]
    hooked-symbol maxInt{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), total{}(), hook{}("INT.max")]
    hooked-symbol ltString{}(SortString{}, SortString{}) : SortBool{} [function{}(), total{}(), hook{}("STRING.lt")]
    hooked-sort SortMInt{S} [hook{}("MINT.MInt"), hasDomainValues{}()]
    sort Sort8{} []
    hooked-symbol ultMInt{}(SortMInt{Sort8{}}, SortMInt{Sort8{}}) : SortBool{} [function{}(), total{}(), hook{}("MINT.ult")]
    hooked-symbol sltMInt{}(SortMInt{Sort8{}}, SortMInt{Sort8{}}) : SortBool{} [function{}(), total{}(), hook{}("MINT.slt")]
    hooked-sort SortMyInt{} [hook{}("INT.Int"), hasDomainValues{}()]
    hooked-symbol gtMyInt{}(SortMyInt{}, SortMyInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.gt")]
    hooked-symbol leMyInt{}(SortMyInt{}, SortMyInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.le")]
    hooked-sort SortMap{}
        [hook{}("MAP.Map"), unit{}(mapUnit{}()), element{}(mapItem{}()), concat{}(mapConcat{}())]
    hooked-symbol mapUnit{}() : SortMap{} [function{}(), total{}(), hook{}("MAP.unit")]
    hooked-symbol mapItem{}(SortInt{}, SortInt{}) : SortMap{} [function{}(), total{}(), hook{}("MAP.element")]
    hooked-symbol mapConcat{}(SortMap{}, SortMap{}) : SortMap{} [function{}(), hook{}("MAP.concat"), assoc{}(), comm{}()]
    hooked-symbol inKeys{}(SortInt{}, SortMap{}) : SortBool{} [function{}(), total{}(), hook{}("MAP.in_keys")]
endmodule []
"#;

fn definition() -> BackendDefinition {
    let syntax = parse_definition(DEFINITION).expect("the definition parses");
    BackendDefinition::internalize(&syntax, "MAIN").expect("the definition internalizes")
}

fn term(definition: &BackendDefinition, source: &str) -> Term {
    definition
        .internalize_term(&parse_pattern(source).expect("the term parses"), &[])
        .expect("the term internalizes")
}

const OPERATORS: [&str; 6] = ["ltInt", "leInt", "gtInt", "geInt", "eqInt", "neInt"];

fn holds(operator: &str, left: i64, right: i64) -> bool {
    match operator {
        "ltInt" => left < right,
        "leInt" => left <= right,
        "gtInt" => left > right,
        "geInt" => left >= right,
        "eqInt" => left == right,
        "neInt" => left != right,
        _ => unreachable!("an operator of OPERATORS"),
    }
}

/// An operand: one of the variables `X`, `Y`, `Z`, a literal, or a variable shifted by a literal
/// (`X +Int k`, or `X -Int -k` for a negative `k`).
#[derive(Clone, Copy, Debug)]
enum Operand {
    Variable(usize),
    Literal(i64),
    Shifted(usize, i64),
    /// `X /Int Y` (truncating), undefined where `Y` is 0: a partial atom.
    Quotient(usize, usize),
    /// `absInt(X)`: an atom with the range facts of `INT.abs`.
    Abs(usize),
    /// `minInt(X, Y +Int k)` and `maxInt(X, Y +Int k)`: atoms with the range facts of `INT.min`
    /// and `INT.max`.
    Min(usize, usize, i64),
    Max(usize, usize, i64),
}

const NAMES: [&str; 3] = ["X", "Y", "Z"];

impl Operand {
    fn kore(self) -> String {
        match self {
            Self::Variable(index) => format!("{}:SortInt{{}}", NAMES[index]),
            Self::Literal(value) => format!(r#"\dv{{SortInt{{}}}}("{value}")"#),
            Self::Shifted(index, offset) if offset < 0 => format!(
                "subInt{{}}({}, {})",
                Self::Variable(index).kore(),
                Self::Literal(-offset).kore()
            ),
            Self::Shifted(index, offset) => format!(
                "addInt{{}}({}, {})",
                Self::Variable(index).kore(),
                Self::Literal(offset).kore()
            ),
            Self::Quotient(left, right) => format!(
                "divInt{{}}({}, {})",
                Self::Variable(left).kore(),
                Self::Variable(right).kore()
            ),
            Self::Abs(index) => format!("absInt{{}}({})", Self::Variable(index).kore()),
            Self::Min(left, right, offset) => format!(
                "minInt{{}}({}, {})",
                Self::Variable(left).kore(),
                Self::Shifted(right, offset).kore()
            ),
            Self::Max(left, right, offset) => format!(
                "maxInt{{}}({}, {})",
                Self::Variable(left).kore(),
                Self::Shifted(right, offset).kore()
            ),
        }
    }

    /// The value at `assignment`, `None` where the operand is undefined.
    fn value(self, assignment: [i64; 3]) -> Option<i64> {
        match self {
            Self::Variable(index) => Some(assignment[index]),
            Self::Literal(value) => Some(value),
            Self::Shifted(index, offset) => Some(assignment[index] + offset),
            Self::Quotient(left, right) => {
                (assignment[right] != 0).then(|| assignment[left] / assignment[right])
            }
            Self::Abs(index) => Some(assignment[index].abs()),
            Self::Min(left, right, offset) => {
                Some(assignment[left].min(assignment[right] + offset))
            }
            Self::Max(left, right, offset) => {
                Some(assignment[left].max(assignment[right] + offset))
            }
        }
    }
}

/// A conjunct: `operator(left, right)` required `polarity`, written under `negations` `notBool`s;
/// `\not` of `operator(left, right)` required true (which holds also where an operand is
/// undefined); or the equality `\equals(X, operand)`.
#[derive(Clone, Debug)]
enum Conjunct {
    Literal {
        operator: &'static str,
        left: Operand,
        right: Operand,
        negations: usize,
        polarity: bool,
    },
    Equality(usize, Operand),
    Negated {
        operator: &'static str,
        left: Operand,
        right: Operand,
    },
    /// `\or` of two conjuncts.
    Either(Box<Conjunct>, Box<Conjunct>),
    /// The ML `\equals(left, right)` of two operands, which holds also where both are undefined.
    Same(Operand, Operand),
}

impl Conjunct {
    fn predicate(&self, definition: &BackendDefinition) -> Predicate {
        match self {
            Self::Literal {
                operator,
                left,
                right,
                negations,
                polarity,
            } => {
                let mut text = format!("{operator}{{}}({}, {})", left.kore(), right.kore());
                for _ in 0..*negations {
                    text = format!("notBool{{}}({text})");
                }
                let boolean = term(definition, &format!(r#"\dv{{SortBool{{}}}}("{polarity}")"#));
                Predicate::Equals(term(definition, &text), boolean)
            }
            Self::Equality(variable, operand) => Predicate::Equals(
                term(definition, &Operand::Variable(*variable).kore()),
                term(definition, &operand.kore()),
            ),
            Self::Negated {
                operator,
                left,
                right,
            } => Predicate::Not(std::sync::Arc::new(
                Self::Literal {
                    operator,
                    left: *left,
                    right: *right,
                    negations: 0,
                    polarity: true,
                }
                .predicate(definition),
            )),
            Self::Either(left, right) => {
                Predicate::Or(vec![left.predicate(definition), right.predicate(definition)].into())
            }
            Self::Same(left, right) => Predicate::Equals(
                term(definition, &left.kore()),
                term(definition, &right.kore()),
            ),
        }
    }

    fn satisfied(&self, assignment: [i64; 3]) -> bool {
        match self {
            Self::Literal {
                operator,
                left,
                right,
                negations,
                polarity,
            } => match (left.value(assignment), right.value(assignment)) {
                (Some(left), Some(right)) => {
                    let value = holds(operator, left, right);
                    (value != (negations % 2 == 1)) == *polarity
                }
                // An undefined comparison is no Boolean: the conjunct does not hold.
                _ => false,
            },
            Self::Equality(variable, operand) => {
                operand.value(assignment) == Some(assignment[*variable])
            }
            Self::Negated {
                operator,
                left,
                right,
            } => !matches!(
                (left.value(assignment), right.value(assignment)),
                (Some(left), Some(right)) if holds(operator, left, right)
            ),
            Self::Either(left, right) => left.satisfied(assignment) || right.satisfied(assignment),
            Self::Same(left, right) => left.value(assignment) == right.value(assignment),
        }
    }
}

/// The assignments brute force tries: `[-5, 5]^3`. The generated literals are `-1` to `1` and the
/// offsets `-2` to `2`, so every bound a conjunct states lies in `[-4, 4]` and a conjunction
/// satisfiable over the integers has a witness here, also one bounded on one side only
/// (`X +Int -2 >Int 1` is `X >= 4`).
fn assignments() -> impl Iterator<Item = [i64; 3]> {
    (-5..=5).flat_map(|x| (-5..=5).flat_map(move |y| (-5..=5).map(move |z| [x, y, z])))
}

/// Checks one conjunction against brute force: `contradictory` only when no assignment in
/// `[-5, 5]^3` satisfies it, and each equality `equalities` returns holds in every assignment
/// that does. Returns the failure.
fn check(definition: &BackendDefinition, conjuncts: &[Conjunct]) -> Option<String> {
    let predicates = conjuncts
        .iter()
        .map(|conjunct| conjunct.predicate(definition))
        .collect::<Vec<_>>();
    let satisfying = assignments()
        .filter(|assignment| {
            conjuncts
                .iter()
                .all(|conjunct| conjunct.satisfied(*assignment))
        })
        .collect::<Vec<_>>();
    if contradictory(definition, &predicates) {
        if let Some(witness) = satisfying.first() {
            return Some(format!(
                "{conjuncts:?} is called contradictory but {witness:?} satisfies it"
            ));
        }
        return None;
    }
    // Each term the conjuncts give a literal's value has that value wherever they hold.
    for (member, literal) in literal_values(definition, &predicates) {
        for assignment in &satisfying {
            let (found, expected) = (
                evaluate(&member, *assignment),
                evaluate(&literal, *assignment),
            );
            if found.is_none() || found != expected {
                return Some(format!(
                    "{conjuncts:?}: {member:?} is given the value {literal:?} but is {found:?} at {assignment:?}"
                ));
            }
        }
    }
    let substitution = equalities_with_bounds(definition, &predicates);
    for assignment in &satisfying {
        for (variable, value) in &substitution {
            let index = NAMES
                .iter()
                .position(|name| variable.name.as_ref() == *name)
                .expect("a variable of the conjunction");
            let evaluated = evaluate(value, *assignment);
            if evaluated != Some(assignment[index]) {
                return Some(format!(
                    "{conjuncts:?}: the equality {} = {value:?} fails at {assignment:?}",
                    variable.name
                ));
            }
        }
    }
    None
}

/// The integer value of a term of the generated conjunctions (variables of `NAMES`, literals,
/// `addInt` and `subInt`) at `assignment`.
fn evaluate(term: &Term, assignment: [i64; 3]) -> Option<i64> {
    match term.kind() {
        TermKind::Variable(variable) => NAMES
            .iter()
            .position(|name| variable.name.as_ref() == *name)
            .map(|index| assignment[index]),
        TermKind::DomainValue { .. } => ground_value(term),
        TermKind::Application {
            symbol, arguments, ..
        } => {
            let left = evaluate(arguments.first()?, assignment)?;
            if symbol.name.as_ref() == "absInt" {
                return Some(left.abs());
            }
            let right = evaluate(arguments.get(1)?, assignment)?;
            match symbol.name.as_ref() {
                "minInt" => Some(left.min(right)),
                "maxInt" => Some(left.max(right)),
                "addInt" => Some(left + right),
                "subInt" => Some(left - right),
                "divInt" => (right != 0).then(|| left / right),
                _ => None,
            }
        }
        _ => None,
    }
}

fn ground_value(term: &Term) -> Option<i64> {
    match term.kind() {
        TermKind::DomainValue { value, .. } => {
            std::str::from_utf8(value.as_bytes()).ok()?.parse().ok()
        }
        _ => None,
    }
}

fn literal(operator: &'static str, left: Operand, right: Operand, polarity: bool) -> Conjunct {
    Conjunct::Literal {
        operator,
        left,
        right,
        negations: 0,
        polarity,
    }
}

const X: Operand = Operand::Variable(0);
const Y: Operand = Operand::Variable(1);

#[test]
fn each_comparison_identity_refutes_exactly_its_complement() {
    let definition = definition();
    // `a <op> b` beside the complementary comparison is contradictory; beside a compatible one
    // it is not.
    let complements = [
        ("ltInt", "geInt", false),
        ("leInt", "gtInt", false),
        ("gtInt", "leInt", false),
        ("geInt", "ltInt", false),
        ("eqInt", "neInt", false),
        ("leInt", "ltInt", true),
        ("geInt", "gtInt", true),
        ("leInt", "geInt", true),
    ];
    for (first, second, compatible) in complements {
        let conjuncts = [literal(first, X, Y, true), literal(second, X, Y, true)];
        let predicates = conjuncts
            .iter()
            .map(|conjunct| conjunct.predicate(&definition))
            .collect::<Vec<_>>();
        assert_eq!(
            contradictory(&definition, &predicates),
            !compatible,
            "{first} beside {second}"
        );
        assert_eq!(check(&definition, &conjuncts), None);
    }
    // The reversed argument order of `>` and `>=`: `X > Y` is `Y < X`, so it refutes `Y >= X`.
    let conjuncts = [literal("gtInt", X, Y, true), literal("geInt", Y, X, true)];
    let predicates = conjuncts
        .iter()
        .map(|conjunct| conjunct.predicate(&definition))
        .collect::<Vec<_>>();
    assert!(contradictory(&definition, &predicates));
}

#[test]
fn atoms_true_wherever_defined_refute_their_negation_only() {
    let definition = definition();
    let required = |text: &str, polarity: bool| {
        Predicate::Equals(
            term(&definition, text),
            term(
                &definition,
                &format!(r#"\dv{{SortBool{{}}}}("{polarity}")"#),
            ),
        )
    };
    let key_in_its_map =
        "inKeys{}(X:SortInt{}, mapConcat{}(mapItem{}(X:SortInt{}, Y:SortInt{}), M:SortMap{}))";
    assert!(contradictory(
        &definition,
        &[required(key_in_its_map, false)]
    ));
    assert!(!contradictory(
        &definition,
        &[required(key_in_its_map, true)]
    ));
    let other_key =
        "inKeys{}(Y:SortInt{}, mapConcat{}(mapItem{}(X:SortInt{}, Y:SortInt{}), M:SortMap{}))";
    assert!(!contradictory(&definition, &[required(other_key, false)]));
    // `A == A` holds wherever defined; `A < A` fails wherever defined.
    assert!(contradictory(
        &definition,
        &[required("eqInt{}(X:SortInt{}, X:SortInt{})", false)]
    ));
    assert!(contradictory(
        &definition,
        &[required("ltInt{}(X:SortInt{}, X:SortInt{})", true)]
    ));
    assert!(!contradictory(
        &definition,
        &[required("leInt{}(X:SortInt{}, X:SortInt{})", true)]
    ));
}

/// A domain value is a Boolean literal only when its sort's domain kind is the Booleans. A token
/// sort or `String` may spell a value `"true"` or `"false"`; such a value is one value of its sort
/// among others, so `T` differing from both spellings is satisfiable (`T = abc`), and the two
/// conjuncts are not complementary. A sort hooked `BOOL.Bool` has only the two values, so there
/// they are.
#[test]
fn only_a_domain_value_of_bool_kind_is_read_as_a_boolean() {
    let definition = definition();
    let differs = |variable: &str, sort: &str, spelling: &str| {
        Predicate::Not(std::sync::Arc::new(Predicate::Equals(
            term(&definition, &format!("{variable}:{sort}{{}}")),
            term(&definition, &format!(r#"\dv{{{sort}{{}}}}("{spelling}")"#)),
        )))
    };
    for (variable, sort) in [("T", "SortMyTok"), ("S", "SortString")] {
        let conjuncts = [
            differs(variable, sort, "true"),
            differs(variable, sort, "false"),
        ];
        assert!(
            !contradictory(&definition, &conjuncts),
            "{sort}: {conjuncts:?}"
        );
    }
    // Over a Bool variable the same shape is a literal: `B` required true beside `B` not
    // required true is contradictory.
    let conjuncts = [
        Predicate::Equals(
            term(&definition, "B:SortBool{}"),
            term(&definition, r#"\dv{SortBool{}}("true")"#),
        ),
        differs("B", "SortBool", "true"),
    ];
    assert!(contradictory(&definition, &conjuncts), "{conjuncts:?}");
    // A sort hooked `BOOL.Bool` holds only `true` and `false`: differing from both is no value.
    let conjuncts = [
        differs("B", "SortMyBool", "true"),
        differs("B", "SortMyBool", "false"),
    ];
    assert!(contradictory(&definition, &conjuncts), "{conjuncts:?}");
}

#[test]
fn equalities_hold_on_every_satisfying_assignment() {
    let definition = definition();
    let conjuncts = [
        Conjunct::Equality(0, Y),
        Conjunct::Equality(1, Operand::Literal(2)),
    ];
    assert_eq!(check(&definition, &conjuncts), None);
    let predicates = conjuncts
        .iter()
        .map(|conjunct| conjunct.predicate(&definition))
        .collect::<Vec<_>>();
    assert_eq!(equalities(&predicates).len(), 2);
}

/// Random conjunctions of two to four conjuncts over `X`, `Y`, `Z` and the literals `-1` to `1`,
/// against brute force. With the default count the run takes well under a second.
pub(crate) fn random_conjunctions_agree_with_brute_force(cases: usize) -> Vec<String> {
    let definition = definition();
    let mut state = 0x5eed_c0d1_u64;
    let mut next = |bound: usize| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        usize::try_from((state >> 33) % u64::try_from(bound).unwrap()).unwrap()
    };
    let mut failures = Vec::new();
    for _ in 0..cases {
        let operand = |next: &mut dyn FnMut(usize) -> usize| {
            if next(4) == 0 {
                Operand::Literal(i64::try_from(next(3)).unwrap() - 1)
            } else {
                Operand::Variable(next(3))
            }
        };
        // A comparison operand may also be shifted; the equalities' operands are not.
        let compared = |next: &mut dyn FnMut(usize) -> usize| {
            if next(4) == 0 {
                Operand::Shifted(next(3), i64::try_from(next(5)).unwrap() - 2)
            } else {
                operand(next)
            }
        };
        let count = 2 + next(3);
        let conjuncts = (0..count)
            .map(|_| {
                if next(6) == 0 {
                    Conjunct::Equality(next(3), operand(&mut next))
                } else {
                    Conjunct::Literal {
                        operator: OPERATORS[next(OPERATORS.len())],
                        left: compared(&mut next),
                        right: compared(&mut next),
                        negations: next(3),
                        polarity: next(2) == 0,
                    }
                }
            })
            .collect::<Vec<_>>();
        if let Some(failure) = check(&definition, &conjuncts) {
            failures.push(failure);
        }
    }
    failures
}

#[test]
fn random_conjunctions_agree_with_brute_force_by_default() {
    let failures = random_conjunctions_agree_with_brute_force(2_000);
    assert!(failures.is_empty(), "{failures:#?}");
}

/// Random conjunctions over linear forms (differences of variables shifted by literals), partial
/// quotients, absolute values and `\not` of comparisons, against brute force: the difference
/// bounds, their definedness discipline and the range facts (module documentation, "linear
/// integer arithmetic").
pub(crate) fn random_linear_conjunctions_agree_with_brute_force(cases: usize) -> Vec<String> {
    let definition = definition();
    let mut state = 0x11ea_c0d1_u64;
    let mut next = |bound: usize| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        usize::try_from((state >> 33) % u64::try_from(bound).unwrap()).unwrap()
    };
    let mut failures = Vec::new();
    for _ in 0..cases {
        let operand = |next: &mut dyn FnMut(usize) -> usize| match next(9) {
            0 => Operand::Literal(i64::try_from(next(5)).unwrap() - 2),
            1 | 2 => Operand::Shifted(next(3), i64::try_from(next(5)).unwrap() - 2),
            // Two quotients by `Y`, `X /Int Y` and `Z /Int Y`, so that conjuncts meet on them
            // and both are undefined at once.
            3 | 4 => Operand::Quotient(if next(2) == 0 { 0 } else { 2 }, 1),
            5 => Operand::Abs(next(3)),
            6 => match next(2) {
                0 => Operand::Min(next(3), next(3), i64::try_from(next(3)).unwrap() - 1),
                _ => Operand::Max(next(3), next(3), i64::try_from(next(3)).unwrap() - 1),
            },
            _ => Operand::Variable(next(3)),
        };
        let count = 2 + next(3);
        let conjunct = |next: &mut dyn FnMut(usize) -> usize| {
            let operator = OPERATORS[next(OPERATORS.len())];
            match next(6) {
                // Half of them between the two quotients, both partial at `Y = 0`.
                5 if next(2) == 0 => {
                    Conjunct::Same(Operand::Quotient(0, 1), Operand::Quotient(2, 1))
                }
                5 => Conjunct::Same(operand(next), operand(next)),
                0 | 1 => Conjunct::Negated {
                    operator,
                    left: operand(next),
                    right: operand(next),
                },
                _ => Conjunct::Literal {
                    operator,
                    left: operand(next),
                    right: operand(next),
                    negations: next(2),
                    polarity: next(2) == 0,
                },
            }
        };
        let conjuncts = (0..count)
            .map(|_| {
                if next(4) == 0 {
                    Conjunct::Either(Box::new(conjunct(&mut next)), Box::new(conjunct(&mut next)))
                } else {
                    conjunct(&mut next)
                }
            })
            .collect::<Vec<_>>();
        if let Some(failure) = check(&definition, &conjuncts) {
            failures.push(failure);
        }
    }
    failures
}

#[test]
fn random_linear_conjunctions_agree_with_brute_force_by_default() {
    let failures = random_linear_conjunctions_agree_with_brute_force(4_000);
    assert!(failures.is_empty(), "{failures:#?}");
}

/// V7: using a `\not` comparison of a partial term whose definedness no conjunct shows refutes
/// conjunctions satisfiable where the term is undefined, which the property test sees.
#[test]
fn a_dropped_difference_definedness_guard_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        drop_dbm_definedness_guard: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_linear_conjunctions_agree_with_brute_force(4_000)
    });
    assert!(!failures.is_empty());
}

/// V7: refuting a disjunction when one of its cases is contradictory refutes satisfiable
/// conjunctions, which the property test sees.
#[test]
fn a_misread_disjunction_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        misread_disjunction: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_linear_conjunctions_agree_with_brute_force(4_000)
    });
    assert!(!failures.is_empty());
}

/// V7: reading `minInt` as at least its operands (and `maxInt` as at most them) refutes
/// satisfiable conjunctions (`minInt(X, Y) <Int X` beside `Y <Int X`), which the property test
/// sees.
#[test]
fn a_misread_min_max_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        misread_min_max: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_linear_conjunctions_agree_with_brute_force(4_000)
    });
    assert!(!failures.is_empty());
}

/// V7 (review B round 2): reading an ML `\equals` of two partial terms as showing them defined
/// refutes `\equals(X /Int Y, Z /Int Y)` beside `\not(X /Int Y ==Int Z /Int Y)`, which holds at
/// `Y = 0`; the property test sees it.
#[test]
fn a_misread_equals_definedness_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        misread_equals_definedness: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_linear_conjunctions_agree_with_brute_force(4_000)
    });
    assert!(!failures.is_empty());
}

/// V7: reading an absolute value as at least 1 refutes conjunctions satisfiable at 0, which the
/// property test sees.
#[test]
fn a_misread_range_fact_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        misread_range_fact: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_linear_conjunctions_agree_with_brute_force(4_000)
    });
    assert!(!failures.is_empty());
}

/// V7: reading `a <=Int b` with the wrong orientation refutes satisfiable conjunctions, which the
/// property test sees.
#[test]
fn a_misread_comparison_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        misread_int_le: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_conjunctions_agree_with_brute_force(2_000)
    });
    assert!(!failures.is_empty());
}

/// V7: reading `a <Int b` as `a <=Int b` when bounding one term refutes satisfiable conjunctions
/// (`X <Int 1` required false beside `X <=Int 1` holds at `X = 1`), which the property test sees.
#[test]
fn a_misread_interval_bound_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        misread_interval_bound: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_conjunctions_agree_with_brute_force(2_000)
    });
    assert!(!failures.is_empty());
}

/// A literal under `\not` holds also where its term is undefined: `\not(X in_keys (X |-> Y M))`
/// holds where `M` has the key `X` (the map is undefined), so it refutes nothing alone, and is
/// read as the false literal (which the key's membership contradicts) only beside the absence of
/// `X` from `M` that makes the map defined (KOOL's `lookupMember` pair).
#[test]
fn a_negated_literal_is_read_only_where_its_term_is_shown_defined() {
    let definition = definition();
    let d = &definition;
    let not_holds =
        |text: &str| Predicate::Not(std::sync::Arc::new(Predicate::Term(term(d, text))));
    let in_own_map = not_holds(
        "inKeys{}(X:SortInt{}, mapConcat{}(mapItem{}(X:SortInt{}, Y:SortInt{}), M:SortMap{}))",
    );
    assert!(!contradictory(d, std::slice::from_ref(&in_own_map)));
    let absent = not_holds("inKeys{}(X:SortInt{}, M:SortMap{})");
    assert!(contradictory(d, &[in_own_map, absent]));
    // `\not(Q ==Int Q)` over the partial quotient `Q = X /Int Y` holds where `Y` is 0.
    let quotient = "divInt{}(X:SortInt{}, Y:SortInt{})";
    let not_equal_to_itself = not_holds(&format!("eqInt{{}}({quotient}, {quotient})"));
    assert!(!contradictory(
        d,
        std::slice::from_ref(&not_equal_to_itself)
    ));
    let nonzero = Predicate::Not(std::sync::Arc::new(Predicate::Equals(
        term(d, "Y:SortInt{}"),
        term(d, &int("0")),
    )));
    assert!(contradictory(d, &[not_equal_to_itself, nonzero]));
}

/// V7: merging the operands of a negative equality into one class refutes satisfiable
/// conjunctions (`X =/=Int Y` beside `X ==Int 0` and `Y ==Int 1`), which the property test sees.
#[test]
fn a_misread_literal_class_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        misread_literal_classes: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_conjunctions_agree_with_brute_force(2_000)
    });
    assert!(!failures.is_empty());
}

/// V7: substituting a literal through classes that merge negative equalities gives a term a value
/// it does not have where the conjuncts hold, which the property test sees.
#[test]
fn a_substitution_without_its_class_is_caught_by_the_property_test() {
    let switches = crate::confluence::switches::Switches {
        substitute_without_class: true,
        ..Default::default()
    };
    let failures = crate::confluence::switches::with(switches, || {
        random_conjunctions_agree_with_brute_force(2_000)
    });
    assert!(!failures.is_empty());
}

/// Equalities with literals form classes: two different literals in one class, or a disequality
/// between two members of one class, refute; one literal gives each member its value.
#[test]
fn equality_classes_refute_two_literals_and_give_a_members_value() {
    let definition = definition();
    let d = &definition;
    let string = |value: &str| term(d, &format!(r#"\dv{{SortString{{}}}}("{value}")"#));
    let s = term(d, "S:SortString{}");
    let t = term(d, "T:SortString{}");
    let equals = |left: &Term, right: &Term| Predicate::Equals(left.clone(), right.clone());
    let differs =
        |left: &Term, right: &Term| Predicate::Not(std::sync::Arc::new(equals(left, right)));
    // S = "t", S = "n": two literals of one sort in one class.
    assert!(contradictory(
        d,
        &[equals(&s, &string("t")), equals(&s, &string("n"))]
    ));
    // S = T, T = "t", S =/= "t": a disequality inside a class.
    assert!(contradictory(
        d,
        &[
            equals(&s, &t),
            equals(&t, &string("t")),
            differs(&s, &string("t"))
        ]
    ));
    // S = "t", T = "n", S =/= T: satisfiable.
    let open = [
        equals(&s, &string("t")),
        equals(&t, &string("n")),
        differs(&s, &t),
    ];
    assert!(!contradictory(d, &open));
    assert_eq!(
        literal_values(d, &open),
        vec![(s.clone(), string("t")), (t.clone(), string("n"))]
            .into_iter()
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
    );
    // The same literal twice is one value, not a clash.
    assert!(!contradictory(
        d,
        &[
            equals(&s, &string("t")),
            equals(&t, &string("t")),
            equals(&s, &t)
        ]
    ));
}

fn int(value: &str) -> String {
    format!(r#"\dv{{SortInt{{}}}}("{value}")"#)
}

/// `operator(left, right)` required `polarity`.
fn required(
    definition: &BackendDefinition,
    operator: &str,
    left: &str,
    right: &str,
    polarity: bool,
) -> Predicate {
    Predicate::Equals(
        term(definition, &format!("{operator}{{}}({left}, {right})")),
        term(definition, &format!(r#"\dv{{SortBool{{}}}}("{polarity}")"#)),
    )
}

/// `\not` of `operator(left, right)` required true.
fn not_required(
    definition: &BackendDefinition,
    operator: &str,
    left: &str,
    right: &str,
) -> Predicate {
    Predicate::Not(std::sync::Arc::new(required(
        definition, operator, left, right, true,
    )))
}

const KEY: &str = "X:SortInt{}";

#[test]
fn comparisons_of_one_term_with_literals_are_refuted_by_their_bounds() {
    let definition = definition();
    let d = &definition;
    let refuted = |conjuncts: &[Predicate]| contradictory(d, conjuncts);
    // X >Int 5 beside X <=Int 0: no integer.
    assert!(refuted(&[
        required(d, "gtInt", KEY, &int("5"), true),
        required(d, "leInt", KEY, &int("0"), true),
    ]));
    // X >=Int -5 beside X <Int 0: -5 to -1.
    assert!(!refuted(&[
        required(d, "geInt", KEY, &int("-5"), true),
        required(d, "ltInt", KEY, &int("0"), true),
    ]));
    // X +Int 1 >Int 5 beside X <Int 3: X > 4 and X < 3.
    let shifted = format!("addInt{{}}({KEY}, {})", int("1"));
    assert!(refuted(&[
        required(d, "gtInt", &shifted, &int("5"), true),
        required(d, "ltInt", KEY, &int("3"), true),
    ]));
    // A shift on the left of `+Int` and through `-Int`: (1 +Int X) -Int 2 <Int 0 beside X >Int 0.
    let nested = format!("subInt{{}}(addInt{{}}({}, {KEY}), {})", int("1"), int("2"));
    assert!(refuted(&[
        required(d, "ltInt", &nested, &int("0"), true),
        required(d, "gtInt", KEY, &int("0"), true),
    ]));
    // A literal on the left mirrors the relation: 5 <Int X beside X <Int 6.
    assert!(refuted(&[
        required(d, "ltInt", &int("5"), KEY, true),
        required(d, "ltInt", KEY, &int("6"), true),
    ]));
    // 0 <= X <= 2 with every point excluded; with one point left, not refuted.
    let interval = |excluded: &[&str]| {
        let mut conjuncts = vec![
            required(d, "geInt", KEY, &int("0"), true),
            required(d, "leInt", KEY, &int("2"), true),
        ];
        conjuncts.extend(
            excluded
                .iter()
                .map(|point| required(d, "neInt", KEY, &int(point), true)),
        );
        conjuncts
    };
    assert!(refuted(&interval(&["0", "1", "2"])));
    assert!(!refuted(&interval(&["0", "2"])));
    // An ML equality with a literal: \equals(X, 3) beside X >Int 3.
    assert!(refuted(&[
        Predicate::Equals(term(d, KEY), term(d, &int("3"))),
        required(d, "gtInt", KEY, &int("3"), true),
    ]));
    // Literals beyond i64 are read exactly: X >Int 2^70 beside X <=Int 2^70 is empty, X >=Int 2^70
    // beside X <=Int 2^70 is the point 2^70.
    let big = "1180591620717411303424";
    assert!(refuted(&[
        required(d, "gtInt", KEY, &int(big), true),
        required(d, "leInt", KEY, &int(big), true),
    ]));
    assert!(!refuted(&[
        required(d, "geInt", KEY, &int(big), true),
        required(d, "leInt", KEY, &int(big), true),
    ]));
    // A partial key shown defined by a comparison required true: (X /Int Y) +Int 1 >Int 5 beside
    // X /Int Y <Int 3.
    let quotient = "divInt{}(X:SortInt{}, Y:SortInt{})";
    let shifted_quotient = format!("addInt{{}}({quotient}, {})", int("1"));
    assert!(refuted(&[
        required(d, "gtInt", &shifted_quotient, &int("5"), true),
        required(d, "ltInt", quotient, &int("3"), true),
    ]));
    // A machine-integer or a string comparison bounds no integer. Each conjunction below is
    // satisfiable in its own sort and empty if its values were read as integers: the signed
    // `255p8` is -1, below 1; the string "10" is below "9".
    let word = |value: &str| format!(r#"\dv{{SortMInt{{Sort8{{}}}}}}("{value}")"#);
    assert!(!refuted(&[
        required(d, "sltMInt", "W:SortMInt{Sort8{}}", &word("1p8"), true),
        Predicate::Equals(term(d, "W:SortMInt{Sort8{}}"), term(d, &word("255p8"))),
    ]));
    assert!(!refuted(&[
        required(
            d,
            "ltString",
            "S:SortString{}",
            r#"\dv{SortString{}}("9")"#,
            true
        ),
        Predicate::Equals(
            term(d, "S:SortString{}"),
            term(d, r#"\dv{SortString{}}("10")"#)
        ),
    ]));
}

/// A sort hooked `INT.Int` holds the integers whatever its name, and its literals are read as
/// integers: `X >Int 5` beside `X <=Int 0` over it is refuted.
#[test]
fn comparisons_over_a_sort_hooked_int_are_bounded() {
    let definition = definition();
    let d = &definition;
    let my_int = |value: &str| format!(r#"\dv{{SortMyInt{{}}}}("{value}")"#);
    let key = "X:SortMyInt{}";
    assert!(contradictory(
        d,
        &[
            required(d, "gtMyInt", key, &my_int("5"), true),
            required(d, "leMyInt", key, &my_int("0"), true),
        ]
    ));
    assert!(!contradictory(
        d,
        &[
            required(d, "gtMyInt", key, &my_int("5"), true),
            required(d, "leMyInt", key, &my_int("6"), true),
        ]
    ));
}

/// A `\not` of a comparison also holds where its key is undefined, so it bounds a partial key only
/// where another conjunct shows the key defined; over a variable, which is always defined, it
/// bounds the key.
#[test]
fn a_negated_comparison_bounds_a_partial_term_only_where_it_is_shown_defined() {
    let definition = definition();
    let d = &definition;
    let quotient = "divInt{}(X:SortInt{}, Y:SortInt{})";
    let negated = |key: &str| {
        vec![
            not_required(d, "gtInt", key, &int("5")),
            not_required(d, "ltInt", key, &int("6")),
        ]
    };
    // q <=Int 5 and q >=Int 6, each also true where q = X /Int Y is undefined (Y = 0).
    assert!(!contradictory(d, &negated(quotient)));
    let mut shown = negated(quotient);
    shown.push(required(d, "gtInt", quotient, &int("7"), true));
    assert!(contradictory(d, &shown));
    assert!(contradictory(d, &negated(KEY)));
    // The same with the shape the simplifier leaves for a `notBool` guard, `\not` of the
    // Bool-sorted comparison itself.
    let negated_term = |key: &str| {
        ["gtInt", "ltInt"]
            .into_iter()
            .zip(["5", "6"])
            .map(|(operator, bound)| {
                Predicate::Not(std::sync::Arc::new(Predicate::Term(term(
                    d,
                    &format!("{operator}{{}}({key}, {})", int(bound)),
                ))))
            })
            .collect::<Vec<_>>()
    };
    assert!(!contradictory(d, &negated_term(quotient)));
    let mut shown = negated_term(quotient);
    shown.push(required(d, "gtInt", quotient, &int("7"), true));
    assert!(contradictory(d, &shown));
    assert!(contradictory(d, &negated_term(KEY)));
}
